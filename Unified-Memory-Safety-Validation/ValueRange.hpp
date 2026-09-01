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
 
#ifndef _ValueRange_
#define _ValueRange_
#include "DataflowAnalysis.h"
#include "Utils.hpp"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 
using namespace llvm;
void valueRangeAnalysis(Module *, std::map<const UnifiedMemSafe::VariableMapKeyType *, 
                        UnifiedMemSafe::VariableInfo>, UnifiedMemSafe::AnalysisState, 
                        std::set<const Instruction *> &, pdg::PTAWrapper &);

void tagOperationsForProtections(Module *M, std::set<llvm::Value *> &unsafeSeqPointerSet, pdg::PTAWrapper &PTA);
#endif
