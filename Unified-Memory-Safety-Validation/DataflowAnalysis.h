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
 
#ifndef DATAFLOW_ANALYSIS_H
#define DATAFLOW_ANALYSIS_H

#include <algorithm>
#include <deque>
#include <numeric>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/LoopInfo.h"
//#include "llvm/Analysis/Dominators.h"
#include "Utils.hpp"

#define DEBUG_FDFA(x) if (DebugFDFA) { x; };

namespace llvm {


template<unsigned long Size>
struct DenseMapInfo<std::array<llvm::Instruction*, Size>> {
  using Context = std::array<llvm::Instruction*, Size>;
  static inline Context
  getEmptyKey() {
    Context c;
    std::fill(c.begin(), c.end(),
      llvm::DenseMapInfo<llvm::Instruction*>::getEmptyKey());
    return c;
  }
  static inline Context
  getTombstoneKey() {
    Context c;
    std::fill(c.begin(), c.end(),
      llvm::DenseMapInfo<llvm::Instruction*>::getTombstoneKey());
    return c;
  }
  static unsigned
  getHashValue(const Context& c) {
    return llvm::hash_combine_range(c.begin(), c.end());
  }
  static bool
  isEqual(const Context& lhs, const Context& rhs) {
    return lhs == rhs;
  }
};


}


namespace analysis {


template<typename T>
class WorkList {
public:
  template<typename IterTy>
  WorkList(IterTy i, IterTy e)
    : inList{},
      work{i, e} {
    inList.insert(i,e);
  }

  WorkList()
    : inList{},
      work{}
      { }

  bool empty() const { return work.empty(); }

  bool contains(T elt) const { return inList.count(elt); }

  void
  add(T elt) {
    if (!inList.count(elt)) {
      work.push_back(elt);
    }
  }

  T
  take() {
    T front = work.front();
    work.pop_front();
    inList.erase(front);
    return front;
  }

  std::string toString() const {
    std::string s = std::to_string(work.size()) + "{";
    for (auto elt : work) {
      s += elt->getName().str() + " ";
    }
    s += "}";
    return s;
  }

private:
  llvm::DenseSet<T> inList;
  std::deque<T> work;
};

using BasicBlockWorklist = WorkList<llvm::BasicBlock*>;


// The dataflow analysis computes three different granularities of results.
// An AbstractValue represents information in the abstract domain for a single
// LLVM Value. An AbstractState is the abstract representation of all values
// relevent to a particular point of the analysis. A DataflowResult contains
// the abstract states before and after each instruction in a function. The
// incoming state for one instruction is the outgoing state from the previous
// instruction. For the first instruction in a BasicBlock, the incoming state is
// keyed upon the BasicBlock itself.
//
// Note: In all cases, the AbstractValue should have a no argument constructor
// that builds constructs the initial value within the abstract domain.

template <typename AbstractValue>
using AbstractState = llvm::DenseMap<llvm::Value*,AbstractValue>;


template <typename AbstractValue>
using DataflowResult =
  llvm::DenseMap<llvm::Value*, AbstractState<AbstractValue>>;


template <typename AbstractValue>
bool
operator==(const AbstractState<AbstractValue>& s1,
           const AbstractState<AbstractValue>& s2) {
  if (s1.size() != s2.size()) {
    return false;
  }
  return std::all_of(s1.begin(), s1.end(),
    [&s2] (auto &kvPair) {
      auto found = s2.find(kvPair.first);
      return found != s2.end() && found->second == kvPair.second;
    });
}


template <typename AbstractValue>
AbstractState<AbstractValue>&
getIncomingState(DataflowResult<AbstractValue>& result, llvm::Instruction& i) {
  auto* bb = i.getParent();
  auto* key = (&bb->front() == &i)
    ? static_cast<llvm::Value*>(bb)
    : static_cast<llvm::Value*>(&*--llvm::BasicBlock::iterator{i});
  return result[key];
}


// NOTE: This class is not intended to be used. It is only intended to
// to document the structure of a Transfer policy object as used by the
// DataflowAnalysis class. For a specific analysis, you should implement
// a class with the same interface.
template <typename AbstractValue>
class Transfer {
public:
  void
  operator()(llvm::Value& v, AbstractState<AbstractValue>& s) {
    llvm_unreachable("unimplemented transfer");
  }
};


// This class can be extended with a concrete implementation of the meet
// operator for two elements of the abstract domain. Implementing the
// meetPair() method in the subclass will enable it to be used within the
// general meet operator because of the curiously recurring template pattern.
template <typename AbstractValue, typename SubClass>
class Meet {
public:
  AbstractValue
  operator()(llvm::ArrayRef<AbstractValue> values) {
    return std::accumulate(values.begin(), values.end(),
      AbstractValue(),
      [this] (auto v1, auto v2) {
        return this->asSubClass().meetPair(v1, v2);
      });
  }

  AbstractValue
  meetPair(AbstractValue& v1, AbstractValue& v2) const {
    llvm_unreachable("unimplemented meet");
  }

  AbstractValue 
  intersection(AbstractValue &v1, AbstractValue &v2) const {
    llvm_unreachable("unimplemented meet");
  }

private:
  SubClass& asSubClass() { return static_cast<SubClass&>(*this); };
};


template <typename AbstractValue,
          typename Transfer,
          typename Meet,
          unsigned long ContextSize=1ul>
class ForwardDataflowAnalysis {
public:
  using State   = AbstractState<AbstractValue>;
  using Context = std::array<llvm::Instruction*, ContextSize>;

  using FunctionResults = DataflowResult<AbstractValue>;
  using ContextFunction = std::pair<Context, llvm::Function*>;
  using ContextResults  = llvm::DenseMap<llvm::Function*, FunctionResults>;
  using ContextWorklist = WorkList<ContextFunction>;

  using ContextMapInfo =
    llvm::DenseMapInfo<std::array<llvm::Instruction*, ContextSize>>;
  using AllResults = llvm::DenseMap<Context, ContextResults, ContextMapInfo>;


  ForwardDataflowAnalysis(llvm::Module& m,
                          llvm::ArrayRef<llvm::Function*> entryPoints) {
    for (auto* entry : entryPoints) {
      contextWork.add({Context{0}, entry});
    }
  }


  // computeForwardDataflow collects the dataflow facts for all instructions
  // in the program reachable from the entryPoints passed to the constructor.
  AllResults&
  computeForwardDataflow() {
    while (!contextWork.empty()) {
      auto [context, function] = contextWork.take();
      computeForwardDataflow(*function, context);
    }

    return allResults;
  }

  void printState(State state) {
    for (auto &kv : state) {
      if (llvm::Function *f = llvm::dyn_cast<llvm::Function>(kv.first))
        llvm::errs() << "  Function: " << f->getName() << " -> " <<  kv.second.toString() << "\n";
      else if (llvm::BasicBlock *bb = llvm::dyn_cast<llvm::BasicBlock>(kv.first))
        llvm::errs() << "  BasicBlock: " << bb << " -> " <<  kv.second.toString() << "\n";
      else 
        llvm::errs() << "  " << *kv.first << " -> " <<  kv.second.toString() << "\n";
    }
    llvm::errs() << "\n";
  }

  void constrainValuesByCondition(State &state, llvm::BasicBlock* bb) {
    llvm::BasicBlock *pred = bb->getSinglePredecessor();
    if (pred) {
      if (auto* branch = llvm::dyn_cast<llvm::BranchInst>(pred->getTerminator())) {
        if (branch->isConditional()) {
          auto* condition = branch->getCondition();
          // Get the comparison instruction
          if (llvm::ICmpInst *cmp = llvm::dyn_cast<llvm::ICmpInst>(condition)) {
            llvm::Value *op0 = cmp->getOperand(0);
            llvm::Value *op1 = cmp->getOperand(1);
            llvm::CmpInst::Predicate predicate = cmp->getPredicate();
            bool isTrueBranch = (branch->getSuccessor(0) == bb);
            llvm::ConstantInt *constantOp = nullptr;
            llvm::Value *variableOp = nullptr;
            bool isVariableOpFirst = true;
            if (llvm::isa<llvm::Constant>(op0) && !llvm::isa<llvm::Constant>(op1)) {
              constantOp = llvm::dyn_cast<llvm::ConstantInt>(op0);
              variableOp = op1;
              isVariableOpFirst = false;
            } else if (llvm::isa<llvm::Constant>(op1) && !llvm::isa<llvm::Constant>(op0)) {
              constantOp = llvm::dyn_cast<llvm::ConstantInt>(op1);
              variableOp = op0;
              isVariableOpFirst = true;
            }

            // This means one of the operands is a constant, the other is variable
            if (constantOp && variableOp) {
              state[variableOp] = AbstractValue::getRangeForConditionalBranch(cmp, constantOp, isTrueBranch, isVariableOpFirst);
              if(auto *load = llvm::dyn_cast<llvm::LoadInst>(variableOp)) {
                auto *ptr = load->getPointerOperand();
                if (llvm::isa<llvm::AllocaInst>(ptr->stripPointerCasts())) {
                  state[ptr] = state[variableOp];
                }
              }
            }
          }
        }
      }
    }
  }

  // void updateResults(const State& newState, State& resultsState) {
  //   for (auto &kv : newState) {
  //     auto found = resultsState.find(kv.first);
  //     if (found != resultsState.end()) {
  //       found->second = kv.second;
  //     } else {
  //       resultsState[kv.first] = kv.second;
  //     }
  //   }
  // }

  // computeForwardDataflow collects the dataflowfacts for all instructions
  // within Function f with the associated execution context. Functions whose
  // results are required for the analysis of f will be transitively analyzed.
  DataflowResult<AbstractValue>&
  computeForwardDataflow(llvm::Function& f, const Context& context) {
    // llvm::errs() << "computeForwardDataflow: ";
    // llvm::errs() << f.getName() << " in the context of ";
    // if (context.at(0) == 0)
    //   llvm::errs() << "empty context";
    // else
    //   context.at(0)->print(llvm::errs());
    if (!context.at(0)) {
      DEBUG_FDFA(errs() << "Analyzing function: " << f.getName() << " without context\n";);
    } else {
      DEBUG_FDFA(errs() << "Analyzing function: " << f.getName() << " in the context of" << *context.at(0) << "\n";);
    }

    long depth = 0;
    std::map<llvm::BasicBlock*, long>blackmap;
    active.insert({context, &f});
    //llvm::LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>(f).getLoopInfo();

    // First compute the initial outgoing state of all instructions
    FunctionResults &results = allResults.FindAndConstruct(context).second
                                        .FindAndConstruct(&f).second;
    if (results.find(&f) == results.end()) {
      for (auto bb = f.begin(); bb != f.end(); ++bb) {
        results.FindAndConstruct(&*bb);
      }

      for (auto &i : llvm::instructions(f)) {
        results.FindAndConstruct(&i);
      }
    }
    
    // Add all blocks to the worklist in topological order for efficiency
    llvm::ReversePostOrderTraversal<llvm::Function*> rpot(&f);

    BasicBlockWorklist work(rpot.begin(), rpot.end());

    for (llvm::BasicBlock* BBB : rpot){
      DEBUG_FDFA(llvm::errs() << "BB: " << BBB->getName().str() << "\n";);
      blackmap[BBB] = 0;
    }

    while (!work.empty()) {
      DEBUG_FDFA(llvm::errs() << work.toString() << "\n";);
      auto* bb = work.take();
      DEBUG_FDFA(llvm::errs() << "---- Working on basic block " << bb->getName().str() << " ----\n";);
      
      // Save a copy of the outgoing abstract state to check for changes.
      const auto& oldEntryState = results[bb];
      DEBUG_FDFA(llvm::errs() << "Old Entry State (size=" << oldEntryState.size() << "):\n";);
      DEBUG_FDFA(printState(oldEntryState););

      const auto oldExitState   = results[bb->getTerminator()];
      DEBUG_FDFA(llvm::errs() << "Old Exit State (size=" << oldExitState.size() << "):\n";);
      DEBUG_FDFA(printState(oldExitState););

      // Merge the state coming in from all predecessors
      State state;
      mergeStateFromPredecessors(state, bb, results);
      mergeInState(state, results[&f]);

      DEBUG_FDFA(llvm::errs() << "Merging done\n";);
      DEBUG_FDFA(llvm::errs() << "New Entry State (size=" << state.size() << "):\n";);
      DEBUG_FDFA(printState(state););
      //mergeInState(state, results[&f]);

      if (UsePC) {
        // if this basic block is guarded by a condition, we can use that to
        // constrain the range of some variables
        DEBUG_FDFA(llvm::errs() << "Applying branch conditions\n";);
        State constrainedState;
        constrainValuesByCondition(constrainedState, bb);
        DEBUG_FDFA(llvm::errs() << "Constrained State (size=" << constrainedState.size() << "):\n";);
        DEBUG_FDFA(printState(constrainedState););
        for (auto &kv : constrainedState) {
          // state[kv.first] = kv.second;
          if (state.find(kv.first) == state.end()) {
            state[kv.first] = kv.second;
          } else {
            state[kv.first] = meet.intersection(state[kv.first], kv.second);
          }
        }
        DEBUG_FDFA(llvm::errs() << "Merged Constrained State (size=" << state.size() << "):\n";);
        DEBUG_FDFA(printState(state););
      }

      // If we have already processed the block and no changes have been made to
      // the abstract input, we can skip processing the block. Otherwise, save
      // the new entry state and proceed processing this block.
      if (state == oldEntryState && !state.empty()) {
        DEBUG_FDFA(llvm::errs() << "No changes to entry state, skipping\n";);
        continue;
      }
      results[bb] = state;
      // updateResults(state, results[bb]);

      // Propagate through all instructions in the block
      for (auto& i : *bb) {
        llvm::CallBase *cs = llvm::dyn_cast<llvm::CallBase>(&i);
        if (cs && isAnalyzableCall(cs)) {
          analyzeCall(cs, state, context);
        } else {
          applyTransfer(i, state);
        }

        if (&i == bb->getTerminator()) {
          DEBUG_FDFA(llvm::errs() << "Terminator instruction\n";);
          DEBUG_FDFA(llvm::errs() << "State (size=" << state.size() << "):\n";);
          DEBUG_FDFA(printState(state););
          // For terminator instructions, we save the outgoing state with the
          // basic block so that it can be used as the incoming state for
          // successor blocks.
          // updateResults(state, results[bb->getTerminator()]);
          results[bb->getTerminator()] = state;
          continue;
        }

        auto nextInstItr = BasicBlock::iterator(&i);
        ++nextInstItr;
        Instruction* nextInst = &*nextInstItr;

        results.FindAndConstruct(&i);

        if (state.find(nextInst) != state.end()) {
          results[&i][nextInst] = state[nextInst];
        }
        for (int opIdx = 0; opIdx < nextInst->getNumOperands(); ++opIdx) {
          Value* op = nextInst->getOperand(opIdx);
          if (state.find(op) != state.end()) {
            results[&i][op] = state[op];
          }
        }
        DEBUG_FDFA(llvm::errs() << "After instruction(" << &i << "): " << i << "\n";);
        DEBUG_FDFA(llvm::errs() << "State (size=" << results[&i].size() << "):\n";);
        DEBUG_FDFA(printState(results[&i]););
        // updateResults(state, results[&i]);
      }

      DEBUG_FDFA(llvm::errs() << "New Exit State (size=" << state.size() << "):\n";);
      DEBUG_FDFA(printState(state););

      // If the abstract state for this block did not change, then we are done
      // with this block. Otherwise, we must update the abstract state and
      // consider changes to successors.
      if (state == oldExitState) {
        DEBUG_FDFA(llvm::errs() << "No changes to exit state, skipping\n";);
        continue;
      }
      
      for (auto* s : llvm::successors(bb)) {
        DEBUG_FDFA(llvm::errs() << "Adding successor " << s->getName().str() << "\n";);
        // Seems to be a threshold to avoid infinite loop in some cases
        DEBUG_FDFA(llvm::errs() << "Current Context Depth: " << blackmap[s] << "\n";);
        //LoopInfo *LI = NULL;
        //LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
        //for(llvm::LoopInfo::iterator L = LI.begin(), e = LI.end(); L != e; ++L){
          //if(!(L.contains(&*bb)))
        if(blackmap[s] > 100){
          break;
        }
        else{
          blackmap[s]++;
          work.add(s);
        }
      }

      //llvm::errs() << "Current Context Depth: " << blackmap[bb] << "\n";
      if (auto* ret = llvm::dyn_cast<llvm::ReturnInst>(bb->getTerminator())) {
        results[&f][&f] = meet({results[&f][&f], state[ret->getReturnValue()]});
      }
    }

    // The overall results for the given function and context are updated if
    // necessary. Updating the results for this (function,context) means that
    // all callers must be updated as well.
    auto& oldResults = allResults[context][&f];
    if (!(oldResults == results)) {
      // llvm::errs() << "results changed for function: " << f.getName() << "\n";
      oldResults = results;
      for (auto& caller : callers[{context, &f}]) {
        contextWork.add(caller);
      }
    }

    active.erase({context, &f});
    return results;
  }

  llvm::Function*
  getCalledFunction(llvm::CallBase &cs) {
    auto *calledFunc = cs.getCalledFunction();
    if (!calledFunc) {
      return nullptr;
    }
    auto* calledValue = calledFunc->stripPointerCasts();
    // Currently we do not handle indirect calls but apply transfer directly.
    // To keep soundness, we classify variables in this case as unsafe later in value range analysis
    return llvm::dyn_cast<llvm::Function>(calledValue);
  }

  bool
  isAnalyzableCall(llvm::CallBase *cs) {
    if (!cs) {
      return false;
    }
    auto* called = getCalledFunction(*cs);
    return called && !called->isDeclaration();
  }

  void
  analyzeCall(llvm::CallBase *cs, State &state, const Context& context) {
    Context newContext;
    if (newContext.size() > 0) {
      std::copy(context.begin() + 1, context.end(), newContext.begin());
      newContext.back() = cs;
    }

    auto* caller  = cs->getFunction();
    auto* callee  = getCalledFunction(*cs);
    auto toCall   = std::make_pair(newContext, callee);
    auto toUpdate = std::make_pair(context, caller);

    auto& calledState  = allResults[newContext][callee];
    auto& summaryState = calledState[callee];
    bool needsUpdate   = summaryState.size() == 0;
    unsigned index = 0;
    for (auto& functionArg : callee->args()) {
      auto* passedConcrete = cs->getArgOperand(index);
      auto passedAbstract = state.find(passedConcrete);
      if (passedAbstract == state.end()) {
        transfer(*passedConcrete, state);
        passedAbstract = state.find(passedConcrete);
      }
      auto& arg     = summaryState[&functionArg];
      auto newState = meet({passedAbstract->second, arg});
      needsUpdate |= !(newState == arg);
      arg = newState;
      ++index;
    }

    if (!active.count(toCall) && needsUpdate) {
      computeForwardDataflow(*callee, newContext);
    }

    state[cs] = calledState[callee][callee];
    callers[toCall].insert(toUpdate);
  }

private:
  // These property objects determine the behavior of the dataflow analysis.
  // They should by replaced by concrete implementation classes on a per
  // analysis basis.
  Meet meet;
  Transfer transfer;

  AllResults allResults;
  ContextWorklist contextWork;
  llvm::DenseMap<ContextFunction, llvm::DenseSet<ContextFunction>> callers;
  llvm::DenseSet<ContextFunction> active;

  // balanced: if the states in destination and toMerge do not matach, fill
  // missing ones with unknown states.
  void
  mergeInState(State& destination, const State& toMerge, bool balanced) {
    if (balanced) {
      for (auto& valueStatePair : destination) {
        if (toMerge.find(valueStatePair.first) == toMerge.end()) {
          AbstractValue unknown;
          destination[valueStatePair.first] = unknown;
        }
      }
    }

    for (auto& valueStatePair : toMerge) {
      // If an incoming Value has an AbstractValue in the already merged
      // state, meet it with the new one. Otherwise, copy the new value over,
      // implicitly meeting with bottom.
      auto [found, newlyAdded] = destination.insert(valueStatePair);
      if (!newlyAdded) {
        found->second = meet({found->second, valueStatePair.second});
      } else if (balanced) {
        AbstractValue unknown;
        destination[valueStatePair.first] = unknown;
      }
    }
  }

  void
  mergeInState(State& destination, const State& toMerge) {
    mergeInState(destination, toMerge, false);
  }

  void
  mergeStateFromPredecessors(State &mergedState, llvm::BasicBlock* bb, FunctionResults& results) {
    // errs() << "BB states: \n";
    // printState(results[bb]);
    State state;
    mergeInState(mergedState, results[bb]);
    int i = 0;
    for (auto *p : llvm::predecessors(bb)) {
      DEBUG_FDFA(errs() << "Merging predecessor: " << p->getName() << "\n";);
      if (i == 0) {
        DEBUG_FDFA(errs() << "Merging No.0 predecessor\n";);
        mergeInState(state, results[p->getTerminator()]);
      } else {
        DEBUG_FDFA(errs() << "Merging No." << i << " predecessor\n";);
        mergeInState(state, results[p->getTerminator()], true);
      }
      DEBUG_FDFA(printState(state););

      i++;
    }

    // for (int i = 0, auto p = llvm::predecessors(bb).begin(); p != llvm::predecessors(bb).end(); p++, i++) {
    //   if (i == 0) {
    //     mergeInState(state, results[p->getTerminator()]);
    //     continue;
    //   }

    //   auto predecessorFacts = results[p->getTerminator()];
    //   mergeInState(state, predecessorFacts, true);
    // }
    mergeInState(mergedState, state);
  }

  AbstractValue
  meetOverPHI(State& state, const llvm::PHINode& phi) {
    auto phiValue = AbstractValue();
    for (auto& value : phi.incoming_values()) {
      auto found = state.find(value.get());
      if (state.end() == found) {
        transfer(*value.get(), state);
        found = state.find(value.get());
      }
      phiValue = meet({phiValue, found->second});
    }
    return phiValue;
  }

  void
  applyTransfer(llvm::Instruction& i, State& state) {
    // All phis are explicit meet operations
    if (auto* phi = llvm::dyn_cast<llvm::PHINode>(&i)) {
      state[phi] = meetOverPHI(state, *phi);
    } else {
      transfer(i, state);
    }
  }
};


} // end namespace


#endif
