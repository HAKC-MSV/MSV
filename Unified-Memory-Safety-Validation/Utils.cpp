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
 
#include "Utils.hpp"

cl::opt<std::string> EntryFunction(
    "entry", 
    llvm::cl::desc("Entry Function"),
    cl::init("main")
);

cl::opt<bool> EnableOOWAnalysis(
    "enable-oow", 
    llvm::cl::desc("Enable out of window analysis"),
    cl::init(false)
);

cl::opt<bool> DebugFDFA(
    "debug-fdfa", 
    llvm::cl::desc("Debug forward dataflow analysis"), 
    llvm::cl::init(false)
);

cl::opt<bool> DebugDG(
    "debug-dg", 
    llvm::cl::desc("Debug DataGuard pass"), 
    llvm::cl::init(false)
);

cl::opt<bool> UsePC(
    "use-pc", 
    llvm::cl::desc("Use path condition"), 
    llvm::cl::init(false)
);

cl::opt<bool> DEBUG_SWITCH(
    "enable-debug", 
    llvm::cl::desc("Enable debug mode"), 
    llvm::cl::init(false)
);

cl::opt<bool> DiffOnly(
    "diff-only", 
    llvm::cl::desc("Get the difference between DG and DG--"), 
    llvm::cl::init(false)
);

cl::opt<bool> SFIOnly(
    "sfi-only", 
    llvm::cl::desc("Only protect normal errors with SFI"), 
    llvm::cl::init(false)
);

cl::opt<bool> UseBaggy(
    "use-baggy", 
    llvm::cl::desc("Use baggy as SFI"), 
    llvm::cl::init(true)
);

cl::opt<bool> DebugTaint(
    "debug-taint", 
    llvm::cl::desc("Debug taint analysis"), 
    llvm::cl::init(false)
);

std::string MAGIC_ASM_BEGIN = "addq 123456, %rax";
std::string MAGIC_ASM_END = "addq 654321, %rax";
std::string NORMAL_MAGIC_ASM_BEGIN = "addq 1234567, %rax";
std::string NORMAL_MAGIC_ASM_END = "addq 7654321, %rax";

namespace UnifiedMemSafe { 

int _safeptrscount, _seqptrscount, _dynptrscount, _hasmetadatatableentrycount;
llvm::Type* sizetype;

AnalysisState::AnalysisState() {}

void AnalysisState::SetSizeType(llvm::Type* st) {
    sizetype = st;
}

void AnalysisState::RegisterFunction(Function* func) {
    numFunctions++;
}

void AnalysisState::RegisterVariable(const VariableMapKeyType *Decl) {
    if (Variables.count(Decl)) return;

    Variables[Decl].classification = VariableStates::Safe;
    Variables[Decl].size = llvm::ConstantInt::get(sizetype, 0);
    //errs() << GREEN << "\t=>(Register) Classified " << " as SAFE" << NORMAL << "\n";
    UMS_DEBUG(DEBUG_SWITCH, errs() << GREEN << "\t=>(Register) Classified " << getIdentifyingName(Decl) << " as SAFE" << NORMAL << "\n";);
}
void AnalysisState::ClassifyPointerVariable(const VariableMapKeyType* Decl, VariableStates ptrType) {
    RegisterVariable(Decl);
//    errs()<< GREEN <<"\t=> Current Classification: "<< PtrTypeToString(Variables[Decl].classification) <<"\n";
//    errs() << GREEN <<"Trying to classsify this to "<<PtrTypeToString(ptrType)<<"\n";
    if (Variables[Decl].classification < ptrType) {
        Variables[Decl].classification = ptrType;
        if(Variables[Decl].isGlobal)
            Variables[Decl].didClassificationChange = true;
        //errs() << GREEN << "\t=> Classified " << " as " << PtrTypeToString(ptrType) << NORMAL << "\n";
        UMS_DEBUG(DEBUG_SWITCH, errs() << GREEN << "\t=> Classified " << getIdentifyingName(Decl) << " as " << PtrTypeToString(ptrType) << NORMAL << "\n";);
    }
    // Fix of the Wild GEP instruction get rid of spatial checking.
    // Violated the original CCured classification, adjust if you need.
    else if ((Variables[Decl].classification == VariableStates::Dyn) && (ptrType == VariableStates::Seq))
    {
        Variables[Decl].classification = ptrType;
        if(Variables[Decl].isGlobal)
            Variables[Decl].didClassificationChange = true;
            UMS_DEBUG(DEBUG_SWITCH, errs() << GREEN << "\t=> Classified " << getIdentifyingName(Decl) << " as " << PtrTypeToString(ptrType) << NORMAL << "\n";);
    }
    else {
        //errs() << GRAY << "\t=> Ignored classification of " << " as " << PtrTypeToString(ptrType) << NORMAL << "\n";
        UMS_DEBUG(DEBUG_SWITCH, errs() << GRAY << "\t=> Ignored classification of " << getIdentifyingName(Decl) << " as " << PtrTypeToString(ptrType) << NORMAL << "\n";);
    }
}
VariableInfo * AnalysisState::SetSizeForPointerVariable(const VariableMapKeyType* Decl, Value *size) {
    RegisterVariable(Decl);
    if (size == NULL) {
        // Variables[Decl].hasSize = false;
        Variables[Decl].size = llvm::ConstantInt::get(sizetype, 0);
    } else {
        // Variables[Decl].hasSize = true;
        Variables[Decl].size = size;
    }
    //errs() << GREEN << "\t=> Size of " << *Decl << " set to " << *(Variables[Decl].size) << NORMAL << "\n";
    UMS_DEBUG(DEBUG_SWITCH, errs() << GREEN << "\t=> Size of " << getIdentifyingName(Decl) << " set to " << *(Variables[Decl].size) << NORMAL << "\n";);
    return &(Variables[Decl]);
}
void AnalysisState::SetExplicitSizeVariableForPointerVariable(const VariableMapKeyType *Decl, Value *explicitSize) {
    RegisterVariable(Decl);
    Variables[Decl].hasExplicitSizeVariable = (explicitSize != NULL);
    Variables[Decl].explicitSizeVariable = explicitSize;
    //errs() << GREEN << "\t=> Explicit size variable for " << " set to " << *(Variables[Decl].explicitSizeVariable) << NORMAL << "\n";
    UMS_DEBUG(DEBUG_SWITCH, errs() << GREEN << "\t=> Explicit size variable for " << getIdentifyingName(Decl) << " set to " << *(Variables[Decl].explicitSizeVariable) << NORMAL << "\n";);
}

void AnalysisState::SetInstantiatedExplicitSizeVariable(const VariableMapKeyType *Ref, bool v) {
    RegisterVariable(Ref);
    Variables[Ref].instantiatedExplicitSizeVariable = v;
}

void AnalysisState::SetHasMetadataTableEntry(const VariableMapKeyType *Ref) {
    RegisterVariable(Ref);
    Variables[Ref].hasMetadataTableEntry = true;
}


VariableInfo * AnalysisState::GetPointerVariableInfo(VariableMapKeyType *Decl) {
    //errs() << GRAY << "\tGetting VarInfo for " << getIdentifyingName(Decl) << "... ";
    //errs() << GRAY << "\tGetting VarInfo for " << "... ";
    if (isa<ConstantPointerNull>(Decl)) {
        UMS_DEBUG(DEBUG_SWITCH, errs() << "ConstantPointer NULL type creating new temp variable info.\n" << NORMAL;);
        VariableInfo* info = new VariableInfo;
        //Attempted BUG FIX - ENUM ISSUE ( NEW STRUCT VARIABLE WITH DEFAULT ENUM VALUE WILL APPARENTLY LEAD TO UNDEFINED BEHAVIOUR)
        info->classification = VariableStates::Unknown;
        info->size = llvm::ConstantInt::get(sizetype, 0);
        return info;
    }
    if (Variables.count(Decl)) {
        //errs() << "found.\n" << NORMAL;
        return &(Variables[Decl]);
    }
    //errs() << RED << "NOT FOUND!\n" << NORMAL;
    return NULL;
}

std::string AnalysisState::GetVariablesStateAsString() {
    std::stringstream SS;

    int tot;
    _safeptrscount = _seqptrscount = _dynptrscount = _hasmetadatatableentrycount = 0;
    tot = Variables.size();

    SS << "Found " << numFunctions << " functions.\n";
    SS << "Found " << tot << " pointer variables:\n";

    for (auto iter = Variables.begin(); iter != Variables.end(); ++iter) {
        if (iter->second.classification == VariableStates::Safe) _safeptrscount++;
        else if (iter->second.classification == VariableStates::Seq) _seqptrscount++;
        else if (iter->second.classification == VariableStates::Dyn) _dynptrscount++;


        if (iter->second.hasMetadataTableEntry) _hasmetadatatableentrycount++;
    }
    SS << "-->) TOTAL Safe pointer variables:\t" << _safeptrscount << " (" << (tot > 0 ? _safeptrscount * 1.0 / tot : 0) * 100 << "%)\n";
    SS << "-->) TOTAL Seq pointer variables:\t" << _seqptrscount << " (" << (tot > 0 ? _seqptrscount * 1.0 / tot : 0) * 100 << "%)\n";
    SS << "-->) TOTAL Dyn pointer variables:\t" << _dynptrscount << " (" << (tot > 0 ? _dynptrscount * 1.0 / tot : 0) * 100 << "%)\n";

    return SS.str();
}

int AnalysisState::GetSafePointerCount() {
    return _safeptrscount;
}
int AnalysisState::GetSeqPointerCount() {
    return _seqptrscount;
}
int AnalysisState::GetDynPointerCount() {
    return _dynptrscount;
}
int AnalysisState::GetHasMetadataTableEntryCount() {
    return _hasmetadatatableentrycount;
}

}
