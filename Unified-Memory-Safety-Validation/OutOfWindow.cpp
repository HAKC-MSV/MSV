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
 
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/StringMap.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetFolder.h"
#include "llvm/Analysis/TargetLibraryInfo.h" 
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"

#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"

#include "llvm/IR/DerivedTypes.h"
#include "Utils.hpp"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 
#include "ValueRange.hpp" 
#include "DataGuard.hpp"
#include "Uriah.hpp"
#include "OutOfWindow.h"
//#include "PointerUtils.hpp"


#include <list>
#include <chrono>
#include <time.h>
#include <unistd.h>
using namespace llvm;

#define DEBUG_TYPE "OutOfWindowPass"
#include "llvm/Support/Debug.h"

static llvm::cl::opt<bool> DebugOOW("debug-oow", llvm::cl::desc("Debug OutOfWindow analysis"), llvm::cl::init(false));
#define OOW_DEBUG(x) if (DebugOOW) { x; }


namespace UnifiedMemSafe {
    using namespace llvm;

	static cl::opt<int> windowSize(
		"spec-window",
		cl::desc("Window size"),
		cl::init(200));

    char OutOfWindowPass::ID = 0;
    static RegisterPass<OutOfWindowPass> OOW("oow", "Collecting all memory accesses that are out of the window", false, false);

    bool OutOfWindowPass::isRecursive(const Function &F, CallGraph &CG) {
        // Check memoization cache first
        auto it = recursionCache.find(&F);
        if (it != recursionCache.end()) {
            return it->second;
        }
        
        SmallPtrSet<const Function *, 16> Visited;
        bool result = dfs(&F, &F, CG, Visited);
        
        // Cache the result
        recursionCache[&F] = result;
        return result;
    }
    
    BasicBlock::const_iterator OutOfWindowPass::findInstructionIterator(const CallBase *callInst) {
        const BasicBlock* targetBB = callInst->getParent();
        for (auto it = targetBB->begin(); it != targetBB->end(); ++it) {
            if (&*it == callInst) {
                return it;
            }
        }
        return targetBB->end();
    }

    bool OutOfWindowPass::dfs(const Function *Target, const Function *Current, CallGraph &CG, SmallPtrSet<const Function *, 16> &Visited) {
        if (!Current || Visited.count(Current)) return false;
        Visited.insert(Current);

        if (Current->isIntrinsic()) {
            return false;
        }

        CallGraphNode *CGN = CG[Current];
        for (CallGraphNode::iterator I = CGN->begin(), E = CGN->end(); I != E; ++I) {
            Function *Callee = I->second ? I->second->getFunction() : nullptr;
            if (!Callee || Callee->isDeclaration()) continue;

            if (Callee == Target) return true;  // Found a cycle

            if (dfs(Target, Callee, CG, Visited)) return true;
        }
        return false;
    }
    
    void OutOfWindowPass::analyzeFunction(const Function *F){
        OOW_DEBUG(errs() << "Analyzing function: " << F->getName() << "\n";);
        if (F->isDeclaration()) {
            OOW_DEBUG(errs() << "Function is a declaration, skipping analysis.\n";);
            return;
        }

        for (const BasicBlock &BB : *F) {
            for (BasicBlock::const_iterator inst = BB.begin(); inst != BB.end(); ++inst) {
                if (const CallBase *callInst = dyn_cast<CallBase>(&*inst)) {
                    if (callInst->getCalledFunction() && isRecursive(*callInst->getCalledFunction(), *CG)) {
                        // treat recursive call as a branch
                        int step = 0;
                        explore(inst, &step);
                    } else if (!callInst->getCalledFunction()) {
                        // treat indirect call as a branch
                        int step = 0;
                        explore(inst, &step);
                    }
                }
            }
        }

        for (auto &BB : *F) {
            const BranchInst *BI = dyn_cast<BranchInst>(BB.getTerminator());
            const SwitchInst *SI = dyn_cast<SwitchInst>(BB.getTerminator());
            if (BI && BI->isConditional()) {
                OOW_DEBUG(errs() << "Found conditional branch in block ";
                BB.begin()->print(errs());
                errs() << "\n";);
                for (unsigned i = 0; i < BI->getNumSuccessors(); ++i) {
                    BasicBlock *Succ = BI->getSuccessor(i);
                    OOW_DEBUG(errs() << "Exploring branch to: ";
                    Succ->begin()->print(errs());
                    errs() << "\n";);
                    int step = 0;
                    BasicBlock::const_iterator inst = Succ->begin();
                    explore(inst, &step);
                    callStack.clear();
                }
            } else if (SI) {
                OOW_DEBUG(errs() << "Found switch in block: ";
                BB.begin()->print(errs());
                errs() << "\n";);
                for (auto &casePair : SI->cases()) {
                    const BasicBlock *Succ = casePair.getCaseSuccessor();
                    OOW_DEBUG(errs() << "Exploring switch case to: ";
                    Succ->begin()->print(errs());
                    errs() << "\n";);
                    int step = 0;
                    BasicBlock::const_iterator inst = Succ->begin();
                    explore(inst, &step);
                    callStack.clear();
                }
            }
        }
    }

    void OutOfWindowPass::explore(BasicBlock::const_iterator inst, int *step) {
        const BasicBlock *BB = inst->getParent();
        
        // Prevent infinite loops by tracking visited instructions at this step level
        auto visitKey = std::make_pair(&*inst, *step);
        if (visitedInstructions.count(visitKey)) {
            return;
        }
        visitedInstructions.insert(visitKey);

        while (*step < windowSize) {
            if (inst == BB->end()) {
                OOW_DEBUG(errs() << "Reached end of basic block: ";
                BB->begin()->print(errs());
                errs() << "\n";);
                if (const SwitchInst *SI = dyn_cast<SwitchInst>(BB->getTerminator())) {
                    OOW_DEBUG(errs() << "Found switch in block: ";
                    BB->begin()->print(errs());
                    errs() << "\n";);
                    return; // No successors to explore
                }

                if (const BranchInst *BI = dyn_cast<BranchInst>(BB->getTerminator())) {
                    if (BI->isConditional()) {
                        OOW_DEBUG(errs() << "Found conditional branch in block: ";
                        BB->begin()->print(errs());
                        errs() << "\n";);
                        return; // Stop exploration on conditional branches
                    }
                }

                if (const InvokeInst *II = dyn_cast<InvokeInst>(BB->getTerminator())) {
                    OOW_DEBUG(errs() << "Found invoke instruction in block: ";
                    BB->begin()->print(errs());
                    errs() << "\n";);
                    if(!II->getCalledFunction() || (II->getCalledFunction() && II->getCalledFunction()->isDeclaration())) {
                        const BasicBlock *normalDest = II->getNormalDest();
                        const BasicBlock *unwindDest = II->getUnwindDest();
                        OOW_DEBUG(errs() << "Normal destination: ";
                        normalDest->begin()->print(errs());
                        errs() << "\n";
                        errs() << "Unwind destination: ";
                        unwindDest->begin()->print(errs());
                        errs() << "\n";);

                        std::vector<const CallBase *> oldCallStack = callStack;
                        int stepFreeze = *step;

                        (*step)++;
                        explore(normalDest->begin(), step);

                        *step = stepFreeze;
                        callStack = oldCallStack;

                        if (unwindDest != normalDest) {
                            explore(unwindDest->begin(), step);
                        }

                        return;
                    }
                }
                
                auto *nextBB = BB->getSingleSuccessor();
                inst = nextBB ? nextBB->begin() : BB->end();
                if (inst == BB->end()) {
                    OOW_DEBUG(errs() << "No more BB to explore, checking call stack.\n";);
                    if (callStack.empty()) {
                        if (isRecursive(*BB->getParent(), *CG)) {
                            return;
                        }
                        OOW_DEBUG(errs() << "Call stack is empty, returning.\n";);
                        if (functionCallSiteMap.find(BB->getParent()) == functionCallSiteMap.end()) {
                            return; // No caller to explore
                        }
                        std::set<const CallBase *> callSites = functionCallSiteMap[BB->getParent()];
                        int stepFreeze = *step;
                        for (auto csIt = callSites.begin(); csIt != callSites.end(); ++csIt) {
                            if (isRecursive(*(*csIt)->getParent()->getParent(), *CG)) {
                                OOW_DEBUG(errs() << "Skipping recursive call site: " << **csIt << "\n";);
                                continue; // Skip recursive calls
                            }
                            if (auto *callInst = dyn_cast<CallInst>(*csIt)) {
                                OOW_DEBUG(errs() << "Exploring normal call site: " << **csIt << "\n";);
                                const CallBase *targetInst = *csIt;

                                BasicBlock::const_iterator it = findInstructionIterator(targetInst);
                                if (it != targetInst->getParent()->end()) {
                                    explore(++it, step);
                                    *step = stepFreeze;
                                    callStack.clear();
                                }
                            } else if (auto *invokeInst = dyn_cast<InvokeInst>(*csIt)) {
                                OOW_DEBUG(errs() << "Exploring invoke call site: " << **csIt << "\n";);
                                const BasicBlock *normalBB = invokeInst->getNormalDest();
                                OOW_DEBUG(errs() << "Normal destination: ";
                                normalBB->begin()->print(errs());
                                errs() << "\n";);
                                inst = normalBB->begin();

                                explore(inst, step);
                                *step = stepFreeze;
                                callStack.clear();

                                const BasicBlock *unwindBB = invokeInst->getUnwindDest();
                                OOW_DEBUG(errs() << "Unwind destination: ";
                                unwindBB->begin()->print(errs());
                                errs() << "\n";);
                                if (unwindBB != normalBB) {
                                    inst = unwindBB->begin();
                                    explore(inst, step);
                                    *step = stepFreeze;
                                    callStack.clear();
                                }
                            }
                        }
                        return;
                    } else {
                        const CallBase *targetInst = callStack.back();
                        const BasicBlock* targetBB = targetInst->getParent();

                        if (auto *callInst = dyn_cast<CallInst>(targetInst)) {
                            OOW_DEBUG(errs() << "Explore call stack, returning to call site (normal call): " << *targetInst << "\n";);
                            BasicBlock::const_iterator it = findInstructionIterator(dyn_cast<CallBase>(targetInst));
                            if (it != targetBB->end()) {
                                inst = ++it;
                            }
                            BB = targetBB;
                            callStack.pop_back();
                            continue;
                        } else if (auto *invokeInst = dyn_cast<InvokeInst>(targetInst)) {
                            OOW_DEBUG(errs() << "Explore call stack, returning to call site (invoke): " << *targetInst << "\n";);
                            const BasicBlock *normalBB = invokeInst->getNormalDest();
                            OOW_DEBUG(errs() << "Normal destination: ";
                            normalBB->begin()->print(errs());
                            errs() << "\n";);
                            inst = normalBB->begin();
                            callStack.pop_back();
                            std::vector<const CallBase *> oldCallStack = callStack;
                            int stepFreeze = *step;

                            explore(inst, step);

                            *step = stepFreeze;
                            callStack = oldCallStack;

                            const BasicBlock *unwindBB = invokeInst->getUnwindDest();
                            OOW_DEBUG(errs() << "Unwind destination: ";
                            unwindBB->begin()->print(errs());
                            errs() << "\n";);
                            if (unwindBB != normalBB) {
                                inst = unwindBB->begin();
                                explore(inst, step);
                            }

                            return;
                        }

                        
                    }
                } else {
                    BB = inst->getParent();
                    OOW_DEBUG(errs() << "Continuing exploration in next basic block: ";
                    BB->begin()->print(errs());
                    errs() << "\n";);
                    continue;
                }
            }

            OOW_DEBUG(errs() << "Inst: " << *inst << " | " << *step << "\n";);

            if (auto *callInst = dyn_cast<CallBase>(inst)) {
                OOW_DEBUG(errs() << "Found call instruction: " << *callInst << "\n";);
                if (callInst->getCalledFunction() && !isRecursive(*callInst->getCalledFunction(), *CG)) {
                    if (!callInst->getCalledFunction()->isDeclaration()) {
                        OOW_DEBUG(errs() << "Entering called function: " << callInst->getCalledFunction()->getName() << "\n";);
                        inst = callInst->getCalledFunction()->begin()->begin();
                        BB = inst->getParent();
                        (*step)++;
                        callStack.push_back(callInst);
                        continue;
                    } else {
                        OOW_DEBUG(errs() << "function is a declaration, skipping analysis.\n";);
                    }
                    if (callInst->getCalledFunction()->getName().startswith("llvm.dbg.")) {
                        OOW_DEBUG(errs() << "Skipping llvm debug function: " << callInst->getCalledFunction()->getName() << "\n";);
                        inst++;
                        continue;
                    }
                } else {
                    OOW_DEBUG(errs() << "indirect call or in recursive call chain, skipping analysis.\n";);
                }
            }

            const Instruction *I = &*inst;
            // if (const CallBase *call = dyn_cast<CallBase>(I)) {
            // 	bool end = analyzeCall(call, step);
            // 	if (end) {
            // 		return; // End exploration on call instructions
            // 	}
            // }

            if (OOWInstructions.find(I) != OOWInstructions.end()) {
                OOWInstructions.erase(I);
            }

            inst++;
            (*step)++;
        }
    }

    bool OutOfWindowPass::runOnModule(Module &M) {
        // Clear caches for fresh analysis
        recursionCache.clear();
        visitedInstructions.clear();
        
        CG = &getAnalysis<CallGraphWrapperPass>().getCallGraph();
        auto *mainFunction = M.getFunction(EntryFunction.getValue());
        if (!mainFunction) {
            errs() << "Unable to find " << EntryFunction.getValue() <<" functions! Skipping!\n" ;
            return false;
        }

        std::set<const llvm::Instruction *> memoryOpSet;
        // add all gep instructions to the set of out-of-window instructions
        // build the call sites map
        for (auto &F : M) {
            for (auto &BB : F) {
                for (auto &I : BB) {
                    if (isa<GetElementPtrInst>(&I)) {
                        OOWInstructions.insert(&I);
                        memoryOpSet.insert(&I);
                    }

                    if (auto *call = dyn_cast<CallBase>(&I)) {
                        auto *calledFunc = call->getCalledFunction();
                        if (!calledFunc) {
                            continue;
                        }

                        if (calledFunc->isDeclaration()) {
                            continue;
                        }
                        
                        functionCallSiteMap[calledFunc].insert(call);
                    }
                }
            }
        }

        // print out function call sites map
        if (DebugOOW) {
            errs() << "Function call sites map:\n";
            for (const auto &pair : functionCallSiteMap) {
                const Function *F = pair.first;
                const std::set<const CallBase *> &callSites = pair.second;
                errs() << "Function: " << F->getName() << " | Call Sites: " << callSites.size() << " | ";
                for (const CallBase *callSite : callSites) {
                    callSite->print(errs());
                    errs() << " | ";
                }
                errs() << "\n";
            }
        }
        
        functionsWillBeAnalyzed.push(mainFunction);
        while (!functionsWillBeAnalyzed.empty()) {
            auto F = functionsWillBeAnalyzed.front();
            functionsWillBeAnalyzed.pop();
            visitedFunctions.insert(F);
            
            analyzeFunction(F);
            
            // Add all called functions to the set for analysis
            for (auto &BB : *F) {
                for (auto &I : BB) {
                    if (auto *callInst = dyn_cast<CallBase>(&I)) {
                        if (Function *calledFunc = callInst->getCalledFunction()) {
                            if (visitedFunctions.find(calledFunc) != visitedFunctions.end()) {
                                continue; // Already visited or in a recursive call chain
                            }
                            functionsWillBeAnalyzed.push(calledFunc);
                        }
                    }
                }
            }
        }

        errs() << "Visited functions: " << visitedFunctions.size() << "\n";
        for (const Function *F : visitedFunctions) {
            errs() << " - " << F->getName() << "\n";
        }

        int unreachable = 0;
        for (const Instruction *I : OOWInstructions) {
            const Function *F = I->getParent()->getParent();
            if (visitedFunctions.find(F) == visitedFunctions.end()) {
                unreachable++;
                OOW_DEBUG(errs() << "Unreachable - ";);
            } else {
                OOW_DEBUG(errs() << "Reachable - ";);
            }
            OOW_DEBUG(errs() << F->getName() << " - ";);
            I->print(errs());
            OOW_DEBUG(errs() << "\n";);
        }
        errs() << "Out-of-window instructions:" << OOWInstructions.size() << "\n";
        errs() << "Unreachable out-of-window functions: " << unreachable << "\n";

        int patternCount = 0;
        int alwaysOutsideCount = 0;
        int variableIndexCount = 0;
        std::set<const GetElementPtrInst *> OOWDSet;
        for (const Instruction *I : memoryOpSet) {
            auto *gep = dyn_cast<GetElementPtrInst>(I);
            if (gep) {
                Value *index = nullptr;
                if (gep->getNumOperands() < 2) {
                    errs() << "GEP with less than 2 operands: " << *gep << "\n";
                    continue;
                } else if (gep->getNumOperands() == 2) {
                    index = gep->getOperand(1);
                } else {
                    index = gep->getOperand(2);
                }

                if (auto *constIndex = dyn_cast<ConstantInt>(index)) {
                    continue;
                } else {
                    variableIndexCount++;
                    OOW_DEBUG(errs() << "Non-constant index in GEP: " << *gep << "\n";);
                    auto *indexLoad = dyn_cast<LoadInst>(index);
                    auto *sextInst = dyn_cast<SExtInst>(index);
                    if (sextInst) {
                        indexLoad = dyn_cast<LoadInst>(sextInst->getOperand(0));
                    }
                    if (indexLoad) {
                        if (auto *indexAddr = dyn_cast<Instruction>(indexLoad->getOperand(0)) ) {
                            bool alwaysOutside = false;
                            bool foundPattern = false;
                            for (auto addrUser : indexAddr->users()) {
                                if (auto *def = dyn_cast<StoreInst>(addrUser)) {
                                    foundPattern = true;
                                    OOW_DEBUG(errs() << "Found pattern in GEP: " << *gep << "\n";);
                                    if (isOutsideWindow(def, gep)) {
                                        alwaysOutside = true;
                                    } else {
                                        break;
                                    }
                                }
                            }
                            if (foundPattern) {
                                patternCount++;
                            }
                            if (alwaysOutside) {
                                OOWDSet.insert(gep);
                                alwaysOutsideCount++;
                                OOW_DEBUG(errs() << "GEP with non-constant index that is always defined outside window: " << *gep << "\n";);
                            }
                        }
                    }
                }
            }
        }

        int OOWDwithoutOOW = 0;

        for (const GetElementPtrInst *gep : OOWDSet) {
            if (OOWInstructions.find(gep) == OOWInstructions.end()) {
                OOWDwithoutOOW++;
            }
        }

        errs() << "Total GEP with non-constant index that is always defined outside window: " << alwaysOutsideCount << "\n";
        errs() << "Total GEP with non-constant index that is defined outside window but not in OOW: " << OOWDwithoutOOW << "\n";
        errs() << "Total GEP with non-constant index that has the patterns: " << patternCount << "\n";
        errs() << "Total GEP with non-constant index: " << variableIndexCount << "\n";

        std::set<const Function *> unreachableFunctions;
        for (auto &F : M) {
            if (visitedFunctions.find(&F) == visitedFunctions.end()) {
                unreachableFunctions.insert(&F);
            }
        }

        errs() << "--------------Unreachable functions start---------------\n";
        for (const Function *F : unreachableFunctions) {
            errs() << F->getName() << "\n";
        }
        errs() << "--------------Unreachable functions end---------------\n";

        return false;
    }

    bool OutOfWindowPass::isOutsideWindow(const Instruction *def, const Instruction *use) {
        const BasicBlock *defBB = def->getParent();
        const BasicBlock *useBB = use->getParent();

        if (defBB == useBB) {
            int defPos = 0, usePos = 0, pos = 0;
            for (const auto &I : *defBB) {
                if (&I == def) defPos = pos;
                if (&I == use) usePos = pos;
                pos++;
            }
            return (usePos - defPos) > windowSize;
        }

        // not in the same BB, BFS to find minimal instruction distance
        std::set<const BasicBlock *> visited;
        std::queue<std::pair<const BasicBlock *, int>> q;
        q.push({defBB, 0});
        visited.insert(defBB);

        while (!q.empty()) {
            auto [bb, dist] = q.front();
            q.pop();
            if (bb == useBB) {
                // Add offset from def to end of defBB, and from begin of useBB to use
                int defOffset = 0, useOffset = 0, pos = 0;
                for (const auto &I : *defBB) {
                    if (&I == def) defOffset = pos;
                    pos++;
                }
                int defBBSize = pos;
                pos = 0;
                for (const auto &I : *useBB) {
                    if (&I == use) useOffset = pos;
                    pos++;
                }
                int totalDist = (defBBSize - defOffset - 1) + dist + useOffset;
                return totalDist > windowSize;
            }
            for (const BasicBlock *succ : successors(bb)) {
                if (visited.insert(succ).second) {
                    q.push({succ, dist + (int)succ->size()});
                }
            }
        }
        return true; // If unreachable, treat as outside window
    }

}

