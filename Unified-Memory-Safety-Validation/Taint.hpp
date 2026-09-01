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
#include "llvm/Analysis/CallGraph.h" 
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"

#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Analysis/CallGraphSCCPass.h"

#include "llvm/IR/DerivedTypes.h"
#include "Utils.hpp"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 
//#include "PointerUtils.hpp"

#include <list>
#include <chrono>
#include <time.h>
#include <unistd.h>
using namespace llvm;

#define DEBUG_TYPE "TaintPass"

namespace UnifiedMemSafe {
	class TaintPass : public ModulePass {

	public:
		TaintPass() : ModulePass(ID) {}
		static char ID; // Pass identification, replacement for typeid
        CallGraph *CG;
		DenseSet<const Value*> ReachableGEPs;
		std::queue<const Value*> Worklist;

		StringRef getPassName() const override { return "TaintPass"; }

	private:
	    pdg::PTAWrapper *PTA;
		Module *CurrentModule;
		std::set<const Function *> functionsWillBeAnalyzed;
		std::set<const Function *> visitedFunctions;
		std::set<const Instruction *> OOWInstructions;
		std::map<const Function *, std::set<const CallBase *>> functionCallSiteMap;
		std::vector<const CallBase *> callStack;

		bool runOnModule(llvm::Module &M) override;

		void getAnalysisUsage(AnalysisUsage &AU) const override{
			AU.addRequired<CallGraphWrapperPass>();
			AU.setPreservesAll();
		}

		void propagateTaint(const Value *V, DenseSet<const Value*> &visited);
		void handleCallInst(const CallBase *callBase, const Value *current);
		void handleLoadInst(const LoadInst *loadInst);
		void handleStoreInst(const StoreInst *storeInst, const Value *current);
		void handleReturnInst(const ReturnInst *returnInst);
	};
}