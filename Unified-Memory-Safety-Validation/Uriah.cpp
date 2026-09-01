
/*
 * 
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
 
#include "Uriah.hpp"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "Utils.hpp"
#include "ValueRange.hpp"
#include "CompatibleType.hpp"
#include "llvm/Analysis/MemoryBuiltins.h"

using namespace llvm;
using namespace UnifiedMemSafe;

bool UnifiedMemSafe::Uriah::isPtrToHeap(llvm::Value* ssaVariable, const llvm::TargetLibraryInfo *TLI, pdg::PTAWrapper &ptaw) {
    int noOperands = -1;
    llvm::Instruction* local = dyn_cast_or_null<Instruction>(ssaVariable);
    if (!local) {
        return false;
    }

    noOperands = local->getNumOperands();

    if (!(ptaw.hasValueNode(*ssaVariable))) {
        return false;
    }

    if (local && TLI) {
        // If it is a call instruction to heap allocation functions
        if (isa<GlobalVariable>(ssaVariable)) {
            return false;
        }

        if (isAllocationFn(local, TLI)) {
            return true;
        }

        if (CallInst *allocationFn = dyn_cast_or_null<CallInst>(local)) {
            if (allocationFn != nullptr && allocationFn->getCalledFunction() != nullptr &&
                (allocationFn->getCalledFunction()->getName().contains("alloc") ||
                 allocationFn->getCalledFunction()->getName().contains("operator new") ||
                 allocationFn->getCalledFunction()->getName().contains("operator new[]"))) {
                return true;
            }
        }

        // Traverse all its operands to see whether it relates to the heap
        for (int j = 0; j < noOperands; j++) {
            // Test if it relates to a Global variable
            if (isa<GlobalVariable>(local->getOperand(j))) {
                return false;
            }

            if (local->getOperand(j) && isAllocationFn(local->getOperand(j), TLI)) {
                return true;
            }

            if (CallInst *operandAlloc = dyn_cast_or_null<CallInst>(local->getOperand(j))) {
                if (operandAlloc->getCalledFunction() != nullptr &&
                    (operandAlloc->getCalledFunction()->getName().contains("alloc") ||
                     operandAlloc->getCalledFunction()->getName().contains("operator new") ||
                     operandAlloc->getCalledFunction()->getName().contains("operator new[]"))) {
                    return true;
                }
            }
        }
    } else {
        SVF::NodeID nodeId = ptaw.getValueNode(*ssaVariable);
        SVF::PointsTo pointsToInfo = ptaw._ander_pta->getPts(nodeId);
        for (auto memObjID = pointsToInfo.begin(); memObjID != pointsToInfo.end(); memObjID++) {
            if (ptaw._ander_pta->getPAG()->getObject(*memObjID)->isHeap()) {
                return true;
            }
        }
        return false;
    }

    return false;
}


Value *UnifiedMemSafe::Uriah::getRootValue(Value *v) {
    Value *root = v;
    
    if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(v)) {
        Value *op = gep->getPointerOperand();
        return getRootValue(op);
    }
    else if (LoadInst *load = dyn_cast<LoadInst>(v)) {
        Value *op = load->getPointerOperand();
        return getRootValue(op);
    }
    else if (AllocaInst *alloca = dyn_cast<AllocaInst>(v)) { // root
        root = alloca;
        return root;
    }
    else if (CallInst *call = dyn_cast_or_null<CallInst>(v)){
        if ((call->getCalledFunction()!=NULL) && call->getCalledFunction()->getName().contains("alloc") && call->arg_size() > 0) {
            Value *arg_0 = call->getArgOperand(0);
            return getRootValue(arg_0);
        }	
    }
    else if (CastInst *cast = dyn_cast<CastInst>(v)) {
        Value *op = cast->getOperand(0);
        return getRootValue(op);
    }

    return root;
}

bool UnifiedMemSafe::Uriah::queryAliasing(Value *v1, Value *v2) {
    
    Value *root1 = getRootValue(v1);
    Value *root2 = getRootValue(v2);

    if (root1 == root2) {
        return true;
    }

    return false;
}

/// -----------------------------------------------------------------------
/// Collect all potential heap pointers & do alias checking (PDG + SVF)
/// -----------------------------------------------------------------------

void UnifiedMemSafe::Uriah::collectHeapPointers(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    AnalysisState &TheState,
    const llvm::TargetLibraryInfo *TLI,
    pdg::PTAWrapper &ptaw,
    pdg::ProgramGraph *pdgraph,
    const std::set<pdg::EdgeType> &edgeTypes,
    std::set<pdg::Node *> &unsafeNode /* out-param */)
{
    for (auto it = TheState.Variables.begin(); it != TheState.Variables.end(); ++it) {
        const Instruction *instruction = dyn_cast_or_null<Instruction>(it->first);
        llvm::Value *ssaVariable = const_cast<UnifiedMemSafe::VariableMapKeyType *>(it->first);

        if (!instruction)
            continue;

        // This SSA variable has nothing to do with heap, discarding
        if (!isPtrToHeap(ssaVariable, TLI, ptaw)) {
            continue;
        }

        // Found pointer to the heap
        heapPointerSet[it->first] = it->second;

        llvm::Function *heapAnalyzeFunction = const_cast<llvm::Instruction *>(instruction)->getFunction();
        llvm::Value *heapPointer = const_cast<llvm::Value *>(it->first);

        // Using PDG for aliasing
        std::set<pdg::EdgeType> edgeTypesCopy = edgeTypes;
        auto *node = pdgraph->getNode(*heapPointer);
        if (!node) 
            continue; // Just in case getNode returns null

        auto &reachable_nodes = pdgraph->findNodesReachedByEdges(*node, edgeTypesCopy);
        for (auto n : reachable_nodes) {
            pdg::GraphNodeType node_type = n->getNodeType();
            if (node_type == pdg::GraphNodeType::INST) {
                unsafeNode.insert(n);
            }
        }

        // Using SVF for aliasing (PDG created based on SVF's Andersen PTA, just use its results)
        auto &aliasInSet = node->getInNeighborsWithDepType(pdg::EdgeType::DATA_ALIAS);
        for (auto aliasNode : aliasInSet) {
            if (aliasNode->getValue() != nullptr) {
                if (UnifiedMemSafe::VariableMapKeyType *mayAliasPointerHeap =
                        dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(aliasNode->getValue()))
                {
                    if (TheState.GetPointerVariableInfo(mayAliasPointerHeap) != nullptr) {
                        UnifiedMemSafe::VariableInfo *aliasVariableInfoHeap = 
                            TheState.GetPointerVariableInfo(mayAliasPointerHeap);
                        heapPointerSet[mayAliasPointerHeap] = *aliasVariableInfoHeap;
                    }
                }
            }
        }

        for (inst_iterator heapinst = inst_begin(*heapAnalyzeFunction), 
                           e = inst_end(*heapAnalyzeFunction);
             heapinst != e; 
             ++heapinst)
        {
            if (heapPointer == &*heapinst)
                continue;

            Instruction *InstMayAliasHeap = &*heapinst;

            if (!(ptaw.hasValueNode(*heapPointer)) ||
                !(ptaw.hasValueNode(*InstMayAliasHeap)))
            {
                continue;
            }

            auto aliasResultHeapOverApproximated = queryAliasing(heapPointer, InstMayAliasHeap);
            if (aliasResultHeapOverApproximated) {
                // errs() << GREEN << "Find Heap Alias: " << *InstMayAliasHeap
                //        << " With: " << *heapPointer << NORMAL << "\n";
                if (UnifiedMemSafe::VariableMapKeyType *mayAliasPointerHeap =
                        dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(InstMayAliasHeap))
                {
                    // errs() << GREEN << "Heap Alias: " << *mayAliasPointerHeap << NORMAL << "\n";
                    if (TheState.GetPointerVariableInfo(mayAliasPointerHeap) != nullptr) {
                        UnifiedMemSafe::VariableInfo *aliasVariableInfoHeap = 
                            TheState.GetPointerVariableInfo(mayAliasPointerHeap);
                        heapPointerSet[mayAliasPointerHeap] = *aliasVariableInfoHeap;
                    }
                }
            }
        }
    }
}


/// -----------------------------------------------------------------------
///  Identify classification of heap objects (seq / dyn) -> unsafe sets
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::identifyHeapObjectClassification(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapSeqPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPtrSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet)
{
    for (auto it = heapPointerSet.begin(); it != heapPointerSet.end(); ++it) {
        if (it->second.classification == UnifiedMemSafe::VariableStates::Dyn ||
            it->second.classification == UnifiedMemSafe::VariableStates::Seq)
        {
            // Mark as unsafe
            unsafeUniqueHeapPointerSet[it->first] = it->second;
            unsafeHeapPointerSet[it->first] = it->second;

            if (it->second.classification == UnifiedMemSafe::VariableStates::Seq) {
                heapSeqPointerSet[it->first] = it->second;
            }
            if (it->second.classification == UnifiedMemSafe::VariableStates::Dyn) {
                heapDynPointerSet[it->first] = it->second;
                if (CastInst *cast = dyn_cast_or_null<CastInst>(const_cast<Value*>(it->first))) {
                    heapDynPtrSet[it->first] = it->second;
                }
            }
        }
    }
}


/// -----------------------------------------------------------------------
///  Identify + classify unsafe heap objects by alias
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::identifyAndClassifyUnsafeHeapObjects(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeAliasHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapSeqPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPtrSet,
    AnalysisState &TheState,
    pdg::PTAWrapper &ptaw,
    pdg::ProgramGraph *pdgraph)
{
    for (auto it = unsafeUniqueHeapPointerSet.begin();
              it != unsafeUniqueHeapPointerSet.end(); 
              ++it)
    {
        const Instruction *instruction = dyn_cast_or_null<Instruction>(it->first);
        if (!instruction) 
            continue;

        Instruction *nonConstInst = const_cast<llvm::Instruction *>(instruction);
        auto node = pdgraph->getNode(*nonConstInst);
        if (!node)
            continue;

        std::unordered_set<Instruction *> aliasSet;

        // Using PDG for aliasing
        auto &aliasSetFromPDG = node->getInNeighborsWithDepType(pdg::EdgeType::DATA_ALIAS);
        for (auto aliasNode : aliasSetFromPDG) {
            auto inst = dyn_cast_or_null<Instruction>(aliasNode->getValue());
            if (inst) { 
                aliasSet.insert(inst);
            }
        }

        llvm::Function *analyzeFunction = const_cast<llvm::Instruction *>(instruction)->getFunction();
        llvm::Value *unsafePointer = const_cast<llvm::Value *>(it->first);

        for (inst_iterator inst = inst_begin(*analyzeFunction), 
                           e = inst_end(*analyzeFunction);
             inst != e;
             ++inst)
        {
            if (unsafePointer == &*inst)
                continue;

            if (aliasSet.find(&*inst) != aliasSet.end()) {
                continue;
            }

            Instruction *InstMayAlias = &*inst;
            if (!(ptaw.hasValueNode(*unsafePointer)) ||
                !(ptaw.hasValueNode(*InstMayAlias)))
            {
                continue;
            }
            // errs() << GREEN << "Querying Heap Alias: " << *InstMayAlias
            //        << " With: " << *unsafePointer << NORMAL << "\n";
            // inefficient, just querying the neighbors
            // auto aliasResult = ptaw.queryAlias(*unsafePointer, *InstMayAlias);
            auto aliasResultOverApproximated = queryAliasing(unsafePointer, InstMayAlias);

            if (aliasResultOverApproximated) {
                aliasSet.insert(InstMayAlias);
                
            }
        }

        for (auto InstMayAlias : aliasSet) {
            if (auto *mayAliasPointer = 
                    dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(InstMayAlias))
            {
                if (TheState.GetPointerVariableInfo(mayAliasPointer) != nullptr) {
                    UnifiedMemSafe::VariableInfo *aliasVariableInfo = 
                        TheState.GetPointerVariableInfo(mayAliasPointer);
                    unsafeHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                    heapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                    if (aliasVariableInfo->classification == UnifiedMemSafe::VariableStates::Seq){
                        unsafeUniqueHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                        heapSeqPointerSet[mayAliasPointer] = *aliasVariableInfo;
                    }
                    else{
                        unsafeAliasHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                    }
                    if (aliasVariableInfo->classification == UnifiedMemSafe::VariableStates::Dyn){
                        unsafeUniqueHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                        heapDynPointerSet[mayAliasPointer] = *aliasVariableInfo;
                        if (CastInst *cast = dyn_cast_or_null<CastInst>(mayAliasPointer)) {
                            heapDynPtrSet[mayAliasPointer] = *aliasVariableInfo;
                        }
                    }
                    else{
                        unsafeAliasHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                    }
                }
            }
        }
    }
}


/// -----------------------------------------------------------------------
///  Find non-aliased heap pointers and representatives among aliased sets
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::findNonAliasedAndRepresentativeHeapPointers(
    const std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    std::set<const llvm::Value *> &NonAliasedHeapPointers,
    pdg::PTAWrapper &ptaw)
{
    std::unordered_map<int, std::set<Value*>> obj_to_instset_map;
    for (auto it = heapPointerSet.begin(); it != heapPointerSet.end(); ++it) {
        if (!isa<CallBase>(it->first)) {
            continue; 
        }
        NonAliasedHeapPointers.insert(it->first);
    }
    // ------------------------------
    //  Identify truly non-aliased calls
    // ------------------------------
    for (auto it1 = heapPointerSet.begin(); it1 != heapPointerSet.end(); ++it1) {
        bool isCallResult = llvm::isa<llvm::CallInst>(it1->first) &&
                            !llvm::isa<llvm::InvokeInst>(it1->first);

        if (!isCallResult)
            continue;

        Value *nonConstVal = const_cast<Value *>(it1->first);
        
        SVF::PointsTo expandedPts;
        ptaw.getExpandedFIPts(*nonConstVal, expandedPts);
        for (auto it = expandedPts.begin(), eit = expandedPts.end(); it != eit; ++it) {
            if (obj_to_instset_map.find(*it) == obj_to_instset_map.end()) {
            obj_to_instset_map[*it] = std::set<Value*>();
            }
            obj_to_instset_map[*it].insert(nonConstVal);
        }

        for (auto it2 = heapPointerSet.begin(); it2 != heapPointerSet.end(); ++it2) {
            if (it1 == it2) continue;
            // if (!(ptaw.hasValueNode(*it1->first)) ||
            //     !(ptaw.hasValueNode(*it2->first)))
            // {
            //     continue;
            // }
            // auto aliasResult = ptaw.queryAlias(
            //     *(const_cast<llvm::Value *>(it1->first)),
            //     *(const_cast<llvm::Value *>(it2->first))
            // );
            auto aliasResultOverApp = queryAliasing(
                const_cast<llvm::Value *>(it1->first), 
                const_cast<llvm::Value *>(it2->first)
            );
            if ((aliasResultOverApp) && isCallResult) {
                NonAliasedHeapPointers.erase(it1->first);
                break;
            }
        }
    }

    std::set<std::set<Value*>> unique_alias_inst_set;
    for (auto it = obj_to_instset_map.begin(), eit = obj_to_instset_map.end(); it != eit; ++it) {
    
        if (unique_alias_inst_set.find(it->second) != unique_alias_inst_set.end())
            continue;
        bool is_subset = false;
        for (auto iter = unique_alias_inst_set.begin(); iter != unique_alias_inst_set.end(); iter++) {
            if (std::includes(iter->begin(), iter->end(), it->second.begin(), it->second.end())) {
            is_subset = true;
            break;
            }

            if (std::includes(it->second.begin(), it->second.end(), iter->begin(), iter->end())) {
            unique_alias_inst_set.erase(iter);
            break;
            }
        }
        if (is_subset)
            continue;
        unique_alias_inst_set.insert(it->second);
    }

    for (const auto& inst_set : unique_alias_inst_set) {
        if (inst_set.size() > 1) {
            for (auto inst : inst_set) {
                NonAliasedHeapPointers.erase(inst);
            }
        }
    }

    // This is confusing, seems to do nothing.
    // ------------------------------
    //  Representatives among aliased sets
    // ------------------------------
    // std::set<const llvm::Value *> processedAliases;
    // for (auto it1 = heapPointerSet.begin(); it1 != heapPointerSet.end(); ++it1) {
    //     // If it1->first is already identified as a truly non-aliased pointer, skip
    //     if (NonAliasedHeapPointers.find(it1->first) != NonAliasedHeapPointers.end())
    //         continue;

    //     bool isRepresentative = true;
    //     bool isCall = llvm::isa<llvm::CallInst>(it1->first) &&
    //                   !llvm::isa<llvm::InvokeInst>(it1->first);

    //     if (!isCall)
    //         continue;

    //     for (auto it2 = heapPointerSet.begin(); it2 != heapPointerSet.end(); ++it2) {
    //         if (it1 == it2) 
    //             continue;

    //         if (!(ptaw.hasValueNode(*it1->first)) ||
    //             !(ptaw.hasValueNode(*it2->first)))
    //         {
    //             continue;
    //         }
    //         auto aliasResult = ptaw.queryAlias(
    //             *(const_cast<llvm::Value *>(it1->first)),
    //             *(const_cast<llvm::Value *>(it2->first))
    //         );
    //         auto aliasResultOverApprox = queryAliasing(
    //             const_cast<llvm::Value *>(it1->first), 
    //             const_cast<llvm::Value *>(it2->first)
    //         );
    //         if ((aliasResult != SVF::NoAlias || aliasResultOverApprox) && isCall) {
    //             if (processedAliases.find(it2->first) != processedAliases.end()) {
    //                 isRepresentative = false;
    //                 break;
    //             }
    //         }
    //     }

    //     if (isRepresentative && isCall) {
    //         NonAliasedHeapPointers.insert(it1->first);
    //         processedAliases.insert(it1->first);
    //     }
    // }
}


/// -----------------------------------------------------------------------
///  Find which allocations in `NonAliasedHeapPointers` are aliased
///    with a given pointer set (seq or dyn).
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::findAliasedAllocations(
    const std::set<const llvm::Value *> &NonAliasedHeapPointers,
    const std::map<const VariableMapKeyType *, VariableInfo> &somePtrSet, 
    std::set<const llvm::Value *> &AliasedResult,
    pdg::PTAWrapper &ptaw, pdg::ProgramGraph *pdgraph)
{
    for (const llvm::Value *ptr : NonAliasedHeapPointers) {
        if (!(ptaw.hasValueNode(*ptr)))
            continue;

        Value *non_const_ptr = const_cast<llvm::Value *>(ptr);
        auto nodePtr = pdgraph->getNode(*non_const_ptr);
        if (!nodePtr) 
            continue;

        for (auto it = somePtrSet.begin(); it != somePtrSet.end(); ++it) {
            if (!(ptaw.hasValueNode(*it->first)))
            {
                continue;
            }

            Value *non_const_val = const_cast<llvm::Value *>(it->first);
            auto node = pdgraph->getNode(*non_const_val);
            if (!node) 
                continue;

            auto &outNeighbors = node->getOutNeighborsWithDepType(pdg::EdgeType::DATA_ALIAS);

            if (outNeighbors.find(nodePtr) != outNeighbors.end()) {
                AliasedResult.insert(ptr);
                break;
            }

            // auto aliasResult = ptaw.queryAlias(
            //     *(const_cast<llvm::Value *>(ptr)),
            //     *(const_cast<llvm::Value *>(it->first))
            // );
            auto aliasResultOA = queryAliasing(
                const_cast<llvm::Value *>(ptr), 
                const_cast<llvm::Value *>(it->first)
            );
            // if (aliasResult != NoAlias) {
            if (aliasResultOA) {
                AliasedResult.insert(ptr);
                break;
            }
        }
    }
}

void Uriah::identifyDifferentKindsOfUnsafeHeapPointers(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    AnalysisState &TheState,
    llvm::Module *CurrentModule,
    const llvm::TargetLibraryInfo *TLI,
    pdg::PTAWrapper &ptaw,
    pdg::ProgramGraph *pdgraph,
    const std::set<pdg::EdgeType> &edgeTypes,
    std::set<const llvm::Value *> &AliasedWithHeapSeqPointers,
    std::set<const llvm::Value *> &AliasedWithHeapDynPointers,
    std::set<const Instruction *> &oowResults)
{
    // ------------------------------------------------------------------
    // Local data structures.
    // ------------------------------------------------------------------
    const Instruction *instruction;

    std::set<const llvm::Value *> NonAliasedHeapPointers;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapSeqPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapDynPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapDynPtrSet; // Need further validation
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> unsafeUniqueHeapPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> unsafeAliasHeapPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> unsafeHeapPointerSet;
    std::set<pdg::Node *> unsafeNode;

    // Make sure PTA info is available
    if (!ptaw.hasPTASetup()) {
        errs() << "Points to info not computed\n";
        return;
    }

    errs() << NORMAL << "-------------IDENTIFYING HEAP POINTERS AND THEIR CLASSIFICATION---------------\n\n";

    auto startTime = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    // ------------------------------------------------------------------
    // 1) Collect all potential heap pointers & do alias checking
    // ------------------------------------------------------------------
    collectHeapPointers(
        heapPointerSet, TheState, TLI, ptaw, pdgraph, edgeTypes, unsafeNode
    );

    auto t1 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for collecting heap pointers and aliasing: " 
           << DETAIL << (t1 - startTime) / 1e9 
           << NORMAL << " seconds\n\n";

    errs() << NORMAL << "Identifing Heap Pointers and Their Classification...\n\n";

    // ------------------------------------------------------------------
    // 2) Identify classification of heap objects (Dyn / Seq)
    // ------------------------------------------------------------------
    identifyHeapObjectClassification(
        heapPointerSet,
        heapSeqPointerSet,
        heapDynPointerSet,
        heapDynPtrSet,
        unsafeUniqueHeapPointerSet,
        unsafeHeapPointerSet
    );

    auto t2 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for identifying heap object classification: " 
           << DETAIL << (t2 - t1) / 1e9 
           << NORMAL << " seconds\n\n";

    errs() << NORMAL << "Identifying Alias Object Classification...\n\n";

    // ------------------------------------------------------------------
    // 3) Identify + classify unsafe heap objects by alias
    // ------------------------------------------------------------------
    identifyAndClassifyUnsafeHeapObjects(
        heapPointerSet,
        unsafeUniqueHeapPointerSet,
        unsafeAliasHeapPointerSet,
        unsafeHeapPointerSet,
        heapSeqPointerSet,
        heapDynPointerSet,
        heapDynPtrSet,
        TheState,
        ptaw,
        pdgraph
    );

    auto t3 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for identifying and classifying unsafe heap objects by alias: " 
           << DETAIL << (t3 - t2) / 1e9 
           << NORMAL << " seconds\n\n";

    // ------------------------------------------------------------------
    // Remove overlap between "originally unsafe" and "alias-unsafe".
    // ------------------------------------------------------------------
    for (auto it = unsafeAliasHeapPointerSet.begin();
              it != unsafeAliasHeapPointerSet.end(); )
    {
        if (unsafeUniqueHeapPointerSet.find(it->first) != unsafeUniqueHeapPointerSet.end())
            unsafeAliasHeapPointerSet.erase(it++);
        else
            ++it;
    }

    // ------------------------------------------------------------------
    // Print stats about total heap pointers.
    // ------------------------------------------------------------------
    errs() << NORMAL << "-------------HEAP MEMORY SAFETY ANALYSIS RESULTS---------------\n\n";
    errs() << GREEN << "Total Heap Pointer Number:\t\t\t\t" 
           << DETAIL << heapPointerSet.size() 
           << NORMAL << "\n";

    /*
    for (const auto &pair : heapPointerSet) {
        const llvm::Value *key = pair.first;

        // Use llvm::dyn_cast to cast the key to an Instruction
        if (const llvm::Instruction *instruction = llvm::dyn_cast<llvm::Instruction>(key)) {
            // Print the instruction using LLVM's print method
            instruction->print(llvm::outs());
            llvm::outs() << "\n";
        } 
    }
    */

    // ------------------------------------------------------------------
    // 4) Identify non-aliased heap pointers and alias representatives
    // ------------------------------------------------------------------
    errs() << NORMAL << "Identifying Non-Aliased Heap Pointers and Alias Representatives...\n\n";
    findNonAliasedAndRepresentativeHeapPointers(
        heapPointerSet,
        NonAliasedHeapPointers,
        ptaw
    );

    auto t4 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for identifying non-aliased heap pointers and alias representatives: " 
           << DETAIL << (t4 - t3) / 1e9 
           << NORMAL << " seconds\n\n";

    // Print stats about the number of allocations
    errs() << GREEN << "Number of Heap Allocations:\t\t\t\t" 
           << DETAIL << NonAliasedHeapPointers.size() 
           << "\n\n";

    // ------------------------------------------------------------------
    // Print + final stats about unsafe pointers
    // ------------------------------------------------------------------
    errs() << GREEN << "CCured Unsafe Heap Pointer Count:\t\t\t" 
           << DETAIL << unsafeUniqueHeapPointerSet.size() 
           << NORMAL << "\n\n";

    //errs() << GREEN << "Unsafe Heap Pointer By Alias:\t\t\t\t" 
           //<< DETAIL << unsafeAliasHeapPointerSet.size() 
           //<< NORMAL << "\n\n";

    /*
    for (const auto &pair : unsafeAliasHeapPointerSet) {
        const llvm::Value *key = pair.first;

        // Use llvm::dyn_cast to cast the key to an Instruction
        if (const llvm::Instruction *instruction = llvm::dyn_cast<llvm::Instruction>(key)) {
            // Print the instruction using LLVM's print method
            instruction->print(llvm::outs());
            llvm::outs() << "\n";
        } 
    }
    */

    errs() << GREEN << "Heap Seq Pointer Count:\t\t\t\t\t" 
           << DETAIL << heapSeqPointerSet.size() 
           << NORMAL << "\n";

    errs() << GREEN << "Heap Dyn Pointer Count:\t\t\t\t\t" 
           << DETAIL << heapDynPointerSet.size() 
           << NORMAL << "\n";

    
    /*
    for (const auto &pair : heapDynPointerSet) {
        const llvm::Value *key = pair.first;

        // Use llvm::dyn_cast to cast the key to an Instruction
        if (const llvm::Instruction *instruction = llvm::dyn_cast<llvm::Instruction>(key)) {
            // Print the instruction using LLVM's print method
            instruction->print(llvm::outs());
            llvm::outs() << "\n";
        } 
    }
    */
    
    // ------------------------------------------------------------------
    // 5) Determine which allocations are aliased with Seq or Dyn pointers
    // ------------------------------------------------------------------
    errs() << NORMAL << "Finding Aliases with Seq Pointers...\n\n";
    findAliasedAllocations(
        NonAliasedHeapPointers, 
        heapSeqPointerSet, 
        AliasedWithHeapSeqPointers, 
        ptaw,
        pdgraph
    );

    auto t5 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for finding aliases with Seq pointers: " 
           << DETAIL << (t5 - t4) / 1e9 
           << NORMAL << " seconds\n\n";

    errs() << NORMAL << "Finding Aliases with Dyn Pointers...\n\n";
    findAliasedAllocations(
        NonAliasedHeapPointers, 
        heapDynPointerSet, 
        AliasedWithHeapDynPointers, 
        ptaw,
        pdgraph
    );
    errs() << NORMAL << "\n";

    auto t6 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for finding aliases with Dyn pointers: " 
           << DETAIL << (t6 - t5) / 1e9 
           << NORMAL << " seconds\n\n";

    // ------------------------------------------------------------------
    // 6) Run value-range analysis and compatible-type analysis
    // ------------------------------------------------------------------
    valueRangeAnalysis(CurrentModule, heapPointerSet, TheState, oowResults, ptaw);

    auto t7 = std::chrono::high_resolution_clock::now().time_since_epoch().count();
    errs() << GREEN << "Time taken for value-range analysis: " 
           << DETAIL << (t7 - t6) / 1e9 
           << NORMAL << " seconds\n\n";

    UnifiedMemSafe::CompatibleType compTypePass;
    compTypePass.safeTypeCastAnalysis(heapDynPtrSet, TheState);
}



