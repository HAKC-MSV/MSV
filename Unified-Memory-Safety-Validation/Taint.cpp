#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Argument.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/DenseSet.h"
#include <queue>

#include "Taint.hpp"

using namespace llvm;

#define DEBUG_TAINT(x) if (DebugTaint) { x; };

namespace UnifiedMemSafe {
    char TaintPass::ID = 0;
    static RegisterPass<TaintPass> X("taint", 
                                        "Interprocedural Taint Analysis Pass", 
                                        false /* Does not modify the CFG */, 
                                        false /* Does not modify the IR */);

    bool TaintPass::runOnModule(Module &M) {
        errs() << "--- Starting Interprocedural Taint Analysis ---\n";

        PTA = &pdg::PTAWrapper::getInstance();
        if (!PTA->hasPTASetup())
            PTA->setupPTA(M);

        // --- 1. Initialization: Seed the Worklist ---
        // First, find the first memory operation after the problematic GEPs

        // 1.1 collect the annotated GEPs
        std::set<const llvm::Value *> dgUnsafeGEPs;
        for (auto &F : M) {
            for (auto &BB : F) {
                for (auto &I : BB) {
                    if (auto *call = dyn_cast<CallInst>(&I)) {
                        llvm::Value *calledVal = call->getCalledOperand();
                        if (auto *asmVal = llvm::dyn_cast<llvm::InlineAsm>(calledVal)) {
                            // Extract the asm string
                            std::string asmStr = asmVal->getAsmString();
                            if (asmStr == MAGIC_ASM_END) {
                                // The next instruction should be the unsafe GEP
                                auto prevInst = call->getPrevNode();
                                if (prevInst && isa<GetElementPtrInst>(prevInst)) {
                                    dgUnsafeGEPs.insert(prevInst);
                                }
                            }
                        }
                    }
                    
                }
            }
        }

        errs() << "Initial GEP sources: " << dgUnsafeGEPs.size() << "\n";

        // 1.2 fix point to find first memory operations
        std::map<const Value*, std::set<const Value *>> firstMemOpMap;
        DenseSet<const Value*> visited;

        for (auto gep : dgUnsafeGEPs) {
            propagateTaint(gep, visited);
            firstMemOpMap[gep] = std::set<const Value *>();
            while (!Worklist.empty()) {
                const Value *current = Worklist.front();
                Worklist.pop();

                for (const User *U : current->users()) {
                    const Instruction *userInst = dyn_cast<Instruction>(U);
                    if (!userInst) continue;
                        
                    if (const LoadInst *LI = dyn_cast<LoadInst>(userInst)) {
                        firstMemOpMap[gep].insert(LI);
                    } else if (const StoreInst *SI = dyn_cast<StoreInst>(userInst)) {
                        if (SI->getPointerOperand() == current) {
                            ReachableGEPs.insert(gep);
                        } else {
                            firstMemOpMap[gep].insert(SI);
                        }
                    } else if (const CallBase *callInst = dyn_cast<CallBase>(userInst)) {
                        Function *calledFunc = callInst->getCalledFunction();
                                    
                        if (calledFunc && !calledFunc->isDeclaration()) {
                            for (unsigned i = 0; i < callInst->arg_size(); ++i) {
                                if (callInst->getArgOperand(i) == current) {
                                    if (i < calledFunc->arg_size()) {
                                        Argument *formalArg = calledFunc->getArg(i);
                                        propagateTaint(formalArg, visited);
                                    }
                                }
                            }
                        }
                    } else if (const ReturnInst *returnInst = dyn_cast<ReturnInst>(userInst)) {
                        Value *retVal = returnInst->getReturnValue();
                        const Function &F = *returnInst->getParent()->getParent();
                        if (retVal) {
                            for (const User *U : F.users()) {
                                if (const CallBase *callInst = dyn_cast<CallBase>(U)) {
                                    propagateTaint(callInst, visited);
                                }
                            }
                        }
                    } else {
                        propagateTaint(userInst, visited);
                    }
                }
            }
        }

        if (DebugTaint) {

        }

        // 1.3 form the sources
        while (!Worklist.empty())
            Worklist.pop();

        std::set<const Value*> addedToWorklist;
        for (auto &memOpPair : firstMemOpMap) {
            DEBUG_TAINT(errs() << "\nInitial Source: " << *memOpPair.first << "\n"; );
            auto &memOps = memOpPair.second;
            for (auto memOp : memOps) {
                DEBUG_TAINT(errs() << "  -- " << *memOp << "\n"; );
                if (!addedToWorklist.count(memOp)) {
                    addedToWorklist.insert(memOp);
                    Worklist.push(memOp);
                }
            }
        }
        

        // --- 2. Find the Fixed-Point with BFS ---
        while (!Worklist.empty()) {
            const Value *current = Worklist.front();
            Worklist.pop();

            // Iterate over all user instructions
            for (const User *U : current->users()) {
                const Instruction *UserInst = dyn_cast<Instruction>(U);
                if (!UserInst) continue;

                if (const CallBase *CI = dyn_cast<CallBase>(UserInst)) {
                    handleCallInst(CI, current);
                } else if (const LoadInst *LI = dyn_cast<LoadInst>(UserInst)) {
                    handleLoadInst(LI);
                } else if (const StoreInst *SI = dyn_cast<StoreInst>(UserInst)) {
                    handleStoreInst(SI, current);
                } else if (const ReturnInst *RI = dyn_cast<ReturnInst>(UserInst)) {
                    handleReturnInst(RI);
                } else {
                    // simple assignment-like propagation
                    propagateTaint(UserInst, ReachableGEPs);
                }
            }
        }

        // --- 3. Output Results ---
        errs() << "\n--- Final Results ---\n";
        
        // int finalGEPCount = 0;
        // for (const Value *V : ReachableGEPs) {
        //     if (isa<GetElementPtrInst>(V)) {
        //         finalGEPCount++;
        //         errs() << "  -> Reached GEP: " << *V << "\n";
        //     }
        // }
        // errs() << "Total number of reachable GEPs (Module-wide): " << finalGEPCount << "\n";

        std::set<const Value *> firstStageGEPs;
        std::set<const Value *> secondStageGEPs;
        std::set<const Value *> branches;

        for (auto gep : dgUnsafeGEPs) {
            if (!ReachableGEPs.count(gep))
                firstStageGEPs.insert(gep);
            else
                secondStageGEPs.insert(gep);
        }

        int taintedGEP = 0;
        for (auto val : ReachableGEPs) {
            if (isa<BranchInst>(val))
                branches.insert(val);
            if (isa<GetElementPtrInst>(val))
                taintedGEP++;
        }

        errs() << "\n\n\nTotal number of tainted GEPs: " << taintedGEP << "\n";

        errs() << "Total number of second stage GEPs: " << secondStageGEPs.size() << "\n";
        for (const Value *V : secondStageGEPs) {
            errs() << "  -- " << *V << "\n";
        }

        errs() << "\n\n\nTotal number of first stage GEPs: " << firstStageGEPs.size() << "\n";
        for (const Value *V : firstStageGEPs) {
            errs() << "  -- " << *V << "\n";
        }

        errs() << "\n\n\nTotal number of tainted branches: " << branches.size() << "\n";
        for (const Value *V : branches) {
            errs() << "  -- " << *V << "\n";
        }

        // 1. add metadata for branches
        // 2. collect all the hardened basic block
        std::set<BasicBlock*> hardenedBB;
        for (auto &F : M) {
            for (auto &BB : F) {
                for (auto &I : BB) {
                    if (secondStageGEPs.count(&I) || branches.count(&I))
                        hardenedBB.insert(&BB);
                    if (branches.count(&I))
                        I.setMetadata("taint.branch", MDNode::get(M.getContext(), {}));
                }
            }
        }

        errs() << "\n\nTotal number of hardened basic blocks: " << hardenedBB.size() << "\n";

        std::set<Instruction *> toBeRemoved;
        for (auto &F : M) {
            for (auto &BB : F) {
                for (auto &I : BB) {
                    if (firstStageGEPs.count(&I)) {
                        auto prevNode = I.getPrevNode();
                        auto nextNode = I.getNextNode();
                        toBeRemoved.insert(prevNode);
                        toBeRemoved.insert(nextNode);
                    }
                    // if (auto *call = dyn_cast<CallInst>(&I)) {
                    //     llvm::Value *calledVal = call->getCalledOperand();
                    //     if (auto *asmVal = llvm::dyn_cast<llvm::InlineAsm>(calledVal)) {
                    //         // Extract the asm string
                    //         std::string asmStr = asmVal->getAsmString();
                    //         if (asmStr == MAGIC_ASM_END) {

                    //             toBeRemoved.push_back(call);
                    //         }
                    //     }
                    // }
                }
            }
        }
        for (auto inst : toBeRemoved) {
            inst->eraseFromParent();
        }

        return false; 
    }

    void TaintPass::propagateTaint(const Value *V, DenseSet<const Value*> &visited) {
        if (V && visited.insert(V).second) {
            Worklist.push(V);
        }
    }

    void TaintPass::handleCallInst(const CallBase *callBase, const Value *current) {
        Function *calledFunc = callBase->getCalledFunction();
                    
        if (calledFunc && !calledFunc->isDeclaration()) {
            // Check if Current is passed as an argument
            for (unsigned i = 0; i < callBase->arg_size(); ++i) {
                if (callBase->getArgOperand(i) == current) {
                    // Propagate taint to the corresponding formal parameter (Argument)
                    if (i < calledFunc->arg_size()) {
                        Argument *FormalArg = calledFunc->getArg(i);
                        propagateTaint(FormalArg, ReachableGEPs);
                    }
                }
            }
        }
    }

    void TaintPass::handleLoadInst(const LoadInst *loadInst) {
        // The result of the load is tainted
        propagateTaint(loadInst, ReachableGEPs);
    }

    void TaintPass::handleStoreInst(const StoreInst *storeInst, const Value *current) {
        DEBUG_TAINT(errs() << "Processing Store: " << *storeInst << "\n";);
        const Value *valueOperand = storeInst->getValueOperand();
        const Value *pointerOperand = storeInst->getPointerOperand();
        if (valueOperand == current) {
            errs() << "Value operand is tainted\n";
            const SVF::PointsTo &objs = PTA->getPts(*pointerOperand);
            for (auto obj : objs) {
                unsigned int base = PTA->getBaseObjectId(obj);
                DEBUG_TAINT(errs() << "  -- " << base << "\n";);
                if(PTA->isHeapObject(base)) {
                    auto mallocCall = PTA->getMalloc(base);
                    if (mallocCall)
                        propagateTaint(mallocCall, ReachableGEPs);
                } else if (PTA->isStackObject(base)) {
                    auto alloca = PTA->getAlloca(base);
                    propagateTaint(alloca, ReachableGEPs);
                } else if (PTA->isGlobalObject(base)) {
                    auto global = PTA->getGlobal(base);
                    propagateTaint(global, ReachableGEPs);
                }
            }
            // **NOTE:** A full analysis would require Alias Analysis to track 
            // stores/loads to/from heap and stack objects.
        }
    }

    void TaintPass::handleReturnInst(const ReturnInst *returnInst) {
        Value *retVal = returnInst->getReturnValue();
        const Function &F = *returnInst->getParent()->getParent();
        if (retVal) {
            for (const User *U : F.users()) {
                if (const CallBase *CB = dyn_cast<CallBase>(U)) {
                    propagateTaint(CB, ReachableGEPs);
                }
            }
        }
    }


}