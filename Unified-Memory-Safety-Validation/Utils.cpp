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

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/IntrinsicInst.h"

#include <algorithm>
#include <fstream>
#include <optional>
#include <set>
#include <tuple>
#include <vector>

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

cl::opt<std::string> YAMLAnalysisOutput(
    "yaml-output",
    llvm::cl::desc("Output file for unsafe source locations in YAML format"),
    llvm::cl::init("msv-analysis.yaml")
);

std::string MAGIC_ASM_BEGIN = "addq 123456, %rax";
std::string MAGIC_ASM_END = "addq 654321, %rax";
std::string NORMAL_MAGIC_ASM_BEGIN = "addq 1234567, %rax";
std::string NORMAL_MAGIC_ASM_END = "addq 7654321, %rax";

namespace UnifiedMemSafe { 

namespace {

struct UnsafeLocationRecord {
    std::optional<std::string> file;
    std::optional<std::string> function;
    std::optional<unsigned> line;
    std::optional<unsigned> column;
    std::optional<std::string> variable;
};

std::set<const llvm::Value *> UnsafeLocationValues;

std::string quoteYamlString(const std::string &value) {
    std::string result;
    result.reserve(value.size() + 2);
    result.push_back('"');

    for (char c : value) {
        switch (c) {
            case '\\': result += "\\\\"; break;
            case '"':  result += "\\\""; break;
            case '\n': result += "\\n"; break;
            case '\r': result += "\\r"; break;
            case '\t': result += "\\t"; break;
            default:   result.push_back(c); break;
        }
    }

    result.push_back('"');
    return result;
}

std::optional<std::string> findSourceVariableName(
    const llvm::Value *V,
    std::set<const llvm::Value *> &visited,
    unsigned depth)
{
    if (!V || depth > 12 || !visited.insert(V).second)
        return std::nullopt;

    llvm::SmallVector<llvm::DbgVariableIntrinsic *, 4> dbgUsers;
    llvm::findDbgUsers(dbgUsers, const_cast<llvm::Value *>(V));
    for (llvm::DbgVariableIntrinsic *dbgUser : dbgUsers) {
        if (!dbgUser || !dbgUser->getVariable())
            continue;

        llvm::StringRef name = dbgUser->getVariable()->getName();
        if (!name.empty())
            return name.str();
    }

    if (const auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(V)) {
        return findSourceVariableName(GEP->getPointerOperand(), visited, depth + 1);
    }

    if (const auto *CI = llvm::dyn_cast<llvm::CastInst>(V)) {
        return findSourceVariableName(CI->getOperand(0), visited, depth + 1);
    }

    if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
        return findSourceVariableName(LI->getPointerOperand(), visited, depth + 1);
    }

    if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
            auto name = findSourceVariableName(PN->getIncomingValue(i), visited, depth + 1);
            if (name)
                return name;
        }
    }

    if (const auto *SI = llvm::dyn_cast<llvm::SelectInst>(V)) {
        auto trueName = findSourceVariableName(SI->getTrueValue(), visited, depth + 1);
        if (trueName)
            return trueName;
        return findSourceVariableName(SI->getFalseValue(), visited, depth + 1);
    }

    return std::nullopt;
}

UnsafeLocationRecord buildUnsafeLocationRecord(const llvm::Value *V) {
    UnsafeLocationRecord record;

    const llvm::Instruction *instruction = llvm::dyn_cast_or_null<llvm::Instruction>(V);
    if (instruction) {
        if (const llvm::Function *F = instruction->getFunction()) {
            if (!F->getName().empty())
                record.function = F->getName().str();
        }

        if (const llvm::DILocation *loc = instruction->getDebugLoc().get()) {
            llvm::StringRef filename = loc->getFilename();
            if (!filename.empty())
                record.file = filename.str();

            if (loc->getLine() != 0)
                record.line = loc->getLine();

            if (loc->getColumn() != 0)
                record.column = loc->getColumn();

            if (llvm::DISubprogram *SP = llvm::getDISubprogram(loc->getScope())) {
                if (!SP->getName().empty())
                    record.function = SP->getName().str();
            }
        }
    } else if (const auto *arg = llvm::dyn_cast_or_null<llvm::Argument>(V)) {
        if (const llvm::Function *F = arg->getParent()) {
            if (!F->getName().empty())
                record.function = F->getName().str();
        }
    }

    std::set<const llvm::Value *> visited;
    record.variable = findSourceVariableName(V, visited, 0);

    return record;
}

void writeOptionalString(std::ofstream &out, const char *key,
                         const std::optional<std::string> &value) {
    out << "    " << key << ": ";
    if (value)
        out << quoteYamlString(*value) << "\n";
    else
        out << "null\n";
}

void writeOptionalUnsigned(std::ofstream &out, const char *key,
                           const std::optional<unsigned> &value) {
    out << "    " << key << ": ";
    if (value)
        out << *value << "\n";
    else
        out << "null\n";
}

} // namespace

void clearUnsafeLocations() {
    UnsafeLocationValues.clear();
}

void recordUnsafeLocation(const llvm::Value *V) {
    if (V)
        UnsafeLocationValues.insert(V);
}

bool writeUnsafeLocationsYaml(const std::string &filename) {
    std::ofstream out(filename, std::ios::out | std::ios::trunc);
    if (!out.is_open())
        return false;

    if (UnsafeLocationValues.empty()) {
        out << "unsafe_locations: []\n";
        return static_cast<bool>(out);
    }

    std::vector<UnsafeLocationRecord> records;
    records.reserve(UnsafeLocationValues.size());
    for (const llvm::Value *V : UnsafeLocationValues)
        records.push_back(buildUnsafeLocationRecord(V));

    std::sort(records.begin(), records.end(),
              [](const UnsafeLocationRecord &lhs, const UnsafeLocationRecord &rhs) {
                  return std::tie(lhs.file, lhs.function, lhs.line, lhs.column, lhs.variable) <
                         std::tie(rhs.file, rhs.function, rhs.line, rhs.column, rhs.variable);
              });

    out << "unsafe_locations:\n";
    for (const UnsafeLocationRecord &record : records) {
        out << "  - file: ";
        if (record.file)
            out << quoteYamlString(*record.file) << "\n";
        else
            out << "null\n";

        writeOptionalString(out, "function", record.function);
        writeOptionalUnsigned(out, "line", record.line);
        writeOptionalUnsigned(out, "column", record.column);
        writeOptionalString(out, "variable", record.variable);
    }

    return static_cast<bool>(out);
}

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
