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
#include "ValueRange.hpp" 
#include "DataGuard.hpp"
#include "Uriah.hpp"
//#include "PointerUtils.hpp"


#include <list>
#include <chrono>
#include <time.h>
#include <unistd.h>
using namespace llvm;

#define IS_DEBUGGING 1
#define IS_NAIVE 0

#define DEBUG_TYPE "OutOfWindowPass"

#define CONTAINS(v, e) (std::find(v.begin(), v.end(), e) != v.end())


namespace UnifiedMemSafe {
	class OutOfWindowPass : public ModulePass {

	public:
		OutOfWindowPass() : ModulePass(ID) {}
		static char ID; // Pass identification, replacement for typeid
        CallGraph *CG;

		StringRef getPassName() const override { return "OutOfWindowPass"; }

        std::set<const Instruction *> &getOOWInstructions() {
            return OOWInstructions;
        }

	private:
		Module *CurrentModule;
		std::queue<const Function *> functionsWillBeAnalyzed;
		std::unordered_set<const Function *> visitedFunctions;
		std::set<const Instruction *> OOWInstructions;
		std::map<const Function *, std::set<const CallBase *>> functionCallSiteMap;
		std::vector<const CallBase *> callStack;
		
		std::unordered_map<const Function *, bool> recursionCache;
		std::set<std::pair<const Instruction *, int>> visitedInstructions;

		void analyzeFunction(const Function *F);

		void explore(BasicBlock::const_iterator inst, int *step);

		bool runOnModule(llvm::Module &M) override;

		void getAnalysisUsage(AnalysisUsage &AU) const override{
			AU.addRequired<CallGraphWrapperPass>();
			AU.setPreservesAll();
		}

		bool isOutsideWindow(const Instruction *def, const Instruction *use);

		bool isRecursive(const Function &F, CallGraph &CG);
		bool dfs(const Function *Target, const Function *Current, CallGraph &CG, SmallPtrSet<const Function *, 16> &Visited);
		
		BasicBlock::const_iterator findInstructionIterator(const CallBase *callInst);
	};
}