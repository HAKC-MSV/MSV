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

#include "llvm/ADT/APSInt.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <bitset>
#include <memory>
#include <string>

#include "DataflowAnalysis.h"
#include "ValueRange.hpp"

#include "Utils.hpp"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 


using namespace llvm;
using std::string;
using std::unique_ptr;

static llvm::cl::opt<bool> DebugVR("debug-vr", llvm::cl::desc("Debug value range analysis"), llvm::cl::init(false));
#define DEBUG_PRINT(x) if (DebugVR) { llvm::errs() << x << "\n"; };

// A small bounding threshold to avoid unbounded expansions
static const uint64_t MAX_RANGE_SIZE = 1024;

// ----------------------------------------------------------------------
// ORIGINAL: Check if pointer is local alloca
// ----------------------------------------------------------------------
static bool isLocalAllocaPointer(Value *ptr) {
    ptr = ptr->stripPointerCasts();
    if (auto *AI = dyn_cast<AllocaInst>(ptr)) {
        return true;
    }
    return false;
}

// ----------------------------------------------------------------------
// UPDATED: Check if pointer is a call to malloc(...). For calls with
//          a non-constant size, we still recognize it as a malloc call
//          but return `nbytes = 0` to indicate unknown size.
// ----------------------------------------------------------------------
static bool isKnownMallocCall(llvm::Value *v, uint64_t &nbytes) {
    if (!v) return false;
    v = v->stripPointerCasts();

    auto *call = dyn_cast<CallBase>(v);
    if (!call) return false;
    Function *callee = call->getCalledFunction();
    if (!callee) return false;
    if (callee->getName() != "malloc") return false;
    // Update the logic here to handle customized allocation wrappers

    if (call->arg_size() < 1) return false;
    if (auto *cint = dyn_cast<ConstantInt>(call->getArgOperand(0))) {
        // Update here as well to reflect the size
        nbytes = cint->getZExtValue();
        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Detected malloc call with size: " << nbytes << "\n";);
    } else {
        // Non-constant allocation size => still recognized as malloc
        nbytes = 0; // Use 0 as a sentinel for "unknown" or variable size
        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Detected malloc call with non-constant size; setting nbytes=0 to indicate unknown size.\n";);
    }
    return true;
}

enum class PossibleRangeValues {
    unknown,
    constant,
    infinity
};

struct RangeValue {
    PossibleRangeValues kind;
    llvm::ConstantInt *lvalue, *rvalue;

    RangeValue() : kind(PossibleRangeValues::unknown),
                   lvalue(nullptr),
                   rvalue(nullptr) {}


    bool isUnknown() const {
        return kind == PossibleRangeValues::unknown;
    }

    bool isInfinity() const {
        return kind == PossibleRangeValues::infinity;
    }

    bool isConstant() const {
        return kind == PossibleRangeValues::constant;
    }

    RangeValue
    operator&(const RangeValue &other) const {
        RangeValue r;
        if (isUnknown() || other.isUnknown()) {
            if (isUnknown()) {
                return other;
            }
            else {
                return *this;
            }
        } else if (isInfinity() || other.isInfinity()) {
            if (isInfinity()) {
                return other;
            }
            else {
                return *this;
            }
        }
        else {
            auto &selfL = lvalue->getValue();
            auto selfL64Bit = selfL.sextOrTrunc(64);
            auto &selfR = rvalue->getValue();
            auto selfR64Bit = selfR.sextOrTrunc(64);
            auto &otherL = (other.lvalue)->getValue();
            auto otherL64Bit = otherL.sextOrTrunc(64);
            auto &otherR = (other.rvalue)->getValue();
            auto otherR64Bit = otherR.sextOrTrunc(64);
            r.kind = PossibleRangeValues::constant;

            if (selfL64Bit.slt(otherL64Bit)) {
                r.lvalue = other.lvalue;
            }
            else {
                r.lvalue = lvalue;
            }

            if (selfR64Bit.sgt(otherR64Bit)) {
                r.rvalue = other.rvalue;
            }
            else {
                r.rvalue = rvalue;
            }
            return r;
        }
    }

    RangeValue
    operator|(const RangeValue &other) const {
        RangeValue r;
        if (isUnknown() || other.isUnknown()) {
            if (isUnknown()) {
                return *this;
            }
            else {
                return other;
            }
        }
        else if (isInfinity() || other.isInfinity()) {
            r.kind = PossibleRangeValues::infinity;
            return r;
        }
        else {
            auto &selfL = lvalue->getValue();
            auto &selfR = rvalue->getValue();
            auto &otherL = (other.lvalue)->getValue();
            auto &otherR = (other.rvalue)->getValue();

            r.kind = PossibleRangeValues::constant;
            if (selfL.slt(otherL)) {
                r.lvalue = lvalue;
            }
            else {
                r.lvalue = other.lvalue;
            }

            if (selfR.sgt(otherR)) {
                r.rvalue = rvalue;
            }
            else {
                r.rvalue = other.rvalue;
            }
            return r;
        }
    }

    bool
    operator==(const RangeValue &other) const {
        if (kind == PossibleRangeValues::constant &&
            other.kind == PossibleRangeValues::constant) {
            auto &selfL = lvalue->getValue();
            auto &selfR = rvalue->getValue();
            auto &otherL = (other.lvalue)->getValue();
            auto &otherR = (other.rvalue)->getValue();
            return selfL == otherL && selfR == otherR;
        }
        else {
            return kind == other.kind;
        }
    }

    std::string toString() const {
        switch (kind) {
            case PossibleRangeValues::unknown:
                return "Unknown";
            case PossibleRangeValues::infinity:
                return "Infinity";
            case PossibleRangeValues::constant:
                std::string res = "Constant: [";
                if (lvalue) {
                    res += std::to_string(lvalue->getType()->getBitWidth());
                    res += ": ";
                    res += std::to_string(lvalue->getValue().getSExtValue());
                } else {
                    res += "null";
                }
                res += ", ";
                if (rvalue) {
                    res += std::to_string(rvalue->getType()->getBitWidth());
                    res += ": ";
                    res += std::to_string(rvalue->getValue().getSExtValue());
                } else {
                    res += "null";
                }
                res += "]";
                return res;
        }
        return "Invalid RangeValue";
    }

    static RangeValue getSignedConstantRange(LLVMContext &context, const APInt &lval, const APInt &rval) {
        RangeValue r;
        r.kind   = PossibleRangeValues::constant;
        r.lvalue = ConstantInt::get(context, lval);
        r.rvalue = ConstantInt::get(context, rval);
        return r;
    }

    static RangeValue getUnsignedConstantRange(LLVMContext &context, const APInt &lval, const APInt &rval) {
        RangeValue r;
        r.kind   = PossibleRangeValues::constant;
        r.lvalue = ConstantInt::get(context, lval);
        r.rvalue = ConstantInt::get(context, rval);
        return r;
    }

    static RangeValue getRangeForConditionalBranch(const ICmpInst *cmp, ConstantInt *constantOp, bool isTrueBranch, bool isVariableOpFirst) {
        CmpInst::Predicate predicate = cmp->getPredicate();
        const APInt &knownAPValue = constantOp->getValue();
        const Type *opType = cmp->getOperand(0)->getType();
        const IntegerType *intTy = dyn_cast<IntegerType>(opType);
        if (!intTy) {
            RangeValue r;
            r.kind = PossibleRangeValues::infinity;
            return r;
        }

        uint32_t bitWidth = intTy->getBitWidth();
        APInt maxVal = APInt::getMaxValue(bitWidth);
        APInt signedMaxVal = APInt::getSignedMaxValue(bitWidth);
        APInt signedMinVal;
        if (knownAPValue.slt(0)) {
            signedMinVal = APInt::getSignedMinValue(bitWidth);
        } else {
            signedMinVal = APInt::getMinValue(bitWidth);
        }
        APInt minVal = APInt::getMinValue(bitWidth);
        
        switch (predicate) {
        case llvm::CmpInst::ICMP_EQ:
            if (isTrueBranch) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue, knownAPValue);
            }
            break;
        case llvm::CmpInst::ICMP_NE:
            if (!isTrueBranch) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue, knownAPValue);
            }
            break;
        case llvm::CmpInst::ICMP_UGT:
            if (isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue + 1, maxVal);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue, maxVal);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue - 1);
            }
            break;
        case llvm::CmpInst::ICMP_UGE:
            if (isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue, maxVal);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue + 1, maxVal);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue - 1);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue);
            }
            break;
        case llvm::CmpInst::ICMP_ULT:
            if (isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue - 1);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue, maxVal);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue + 1, maxVal);
            }
            break;
        case llvm::CmpInst::ICMP_ULE:
            if (isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), minVal, knownAPValue - 1);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue + 1, maxVal);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getUnsignedConstantRange(cmp->getContext(), knownAPValue, maxVal);
            }
            break;
        case llvm::CmpInst::ICMP_SGT:
            if (isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue + 1, signedMaxVal);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue, signedMaxVal);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue - 1);
            }
            break;
        case llvm::CmpInst::ICMP_SGE:
            if (isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue, signedMaxVal);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue + 1, signedMaxVal);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue - 1);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue);
            }  
            break;
        case llvm::CmpInst::ICMP_SLT:
            if (isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue - 1);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue, signedMaxVal);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue + 1, signedMaxVal);
            }
            break;
        case llvm::CmpInst::ICMP_SLE:
            if (isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue);
            } else if (!isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), signedMinVal, knownAPValue - 1);
            } else if (!isTrueBranch && isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue + 1, signedMaxVal);
            } else if (isTrueBranch && !isVariableOpFirst) {
                return getSignedConstantRange(cmp->getContext(), knownAPValue, signedMaxVal);
            }
            break;
        }

        RangeValue r;
        r.kind = PossibleRangeValues::infinity;
        return r;
    }

};

RangeValue makeRange(LLVMContext &context, const APInt &left, const APInt &right) {
    //errs() << "makeRange" << "\n";
    RangeValue r;
    r.kind = PossibleRangeValues::constant;
    r.lvalue = ConstantInt::get(context, left);
    r.rvalue = ConstantInt::get(context, right);
    return r;
}

RangeValue infRange() {
     //errs() << "infRange" << "\n";
    RangeValue r;
    r.kind = PossibleRangeValues::infinity;
    return r;
}

using RangeState  = analysis::AbstractState<RangeValue>;
using RangeResult = analysis::DataflowResult<RangeValue>;

class RangeMeet : public analysis::Meet<RangeValue, RangeMeet> {
public:
    RangeValue
    meetPair(RangeValue &s1, RangeValue &s2) const {
        return s1 | s2;
    }

    RangeValue
    intersection(RangeValue &s1, RangeValue &s2) const {
        // errs() << "Taking intersection of " << s1.toString() << " and " << s2.toString() << "\n";
        return s1 & s2;
    }
};

class RangeTransfer {
public:
    mutable std::unordered_map<llvm::Value*, bool> storeHappened;

    RangeValue getRangeFor(llvm::Value *v, RangeState &state) const {
         //errs() << "getRangeFor" << "\n";
        if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(v)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = constant;
            return r;
        }
        return state[v];
    }

    bool masking(llvm::Value *v) const {
        if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(v)) {
            auto value = constant->getValue();
            value++;
            // errs() << "masking: " << value << "\n";
            return value.isPowerOf2();
        }
        return false;
    }
    
    RangeValue evaluateBinOP(llvm::BinaryOperator &binOp,
                             RangeState &state) const {
        auto *op1 = binOp.getOperand(0);
        auto *op2 = binOp.getOperand(1);
        auto range1 = getRangeFor(op1, state);
        auto range2 = getRangeFor(op2, state);

        auto opcode = binOp.getOpcode();

        if (opcode == Instruction::And 
            && ((range1.isConstant() && masking(op1)) 
            || (range2.isConstant() && masking(op2)))) {
            APInt mask;
            LLVMContext *context;
            if (range1.isConstant() && masking(op1)) {
                context = &((range1.lvalue)->getContext());
                mask = cast<ConstantInt>(op1)->getValue();
            } else {
                context = &((range2.lvalue)->getContext());
                mask = cast<ConstantInt>(op2)->getValue();
            }
            
            APInt ll;
            ll.clearAllBits();

            return makeRange(*context, ll, mask);
        }

        if (range1.isConstant() && range2.isConstant()) {
            // errs() << "Constant Range" << "\n";
            auto l1 = range1.lvalue->getValue();
            l1 = l1.sextOrTrunc(64);
            auto r1 = range1.rvalue->getValue();
            r1 = r1.sextOrTrunc(64);
            auto l2 = range2.lvalue->getValue();
            l2 = l2.sextOrTrunc(64);
            auto r2 = range2.rvalue->getValue();
            r2 = r2.sextOrTrunc(64);

            auto &context = (range1.lvalue)->getContext();
            

            if (opcode == Instruction::Add) {
                bool ofl, ofr;
                auto ll = l1.sadd_ov(l2, ofl);
                auto rr = r1.sadd_ov(r2, ofr);
                if (ofl || ofr) {
                    return infRange();
                }
                else {
                    return makeRange(context, ll, rr);
                }
            }
            else if (opcode == Instruction::Sub) {
                bool ofl, ofr;
                auto ll = l1.ssub_ov(r2, ofl);
                auto rr = r1.ssub_ov(l2, ofr);
                if (ofl || ofr) {
                    return infRange();
                }
                else {
                    return makeRange(context, ll, rr);
                }
            }
            else if (opcode == Instruction::Mul) {
                SmallVector<APInt, 4> candidates;
                bool ofFlags[4];
                candidates.push_back(l1.smul_ov(l2, ofFlags[0]));
                candidates.push_back(l1.smul_ov(r2, ofFlags[1]));
                candidates.push_back(r1.smul_ov(l2, ofFlags[2]));
                candidates.push_back(r1.smul_ov(r2, ofFlags[3]));
                for (auto of:ofFlags) {
                    if (of) {
                        return infRange();
                    }
                }
                auto mx = candidates[0];
                for (auto &x : candidates) {
                    if (x.sgt(mx)) {
                        mx = x;
                    }
                }
                auto mn = candidates[0];
                for (auto &x : candidates) {
                    if (x.slt(mn)) {
                        mn = x;
                    }
                }
                return makeRange(context, mn, mx);
            }
            else if (opcode == Instruction::SDiv) {
                if (l2.isNegative() && r2.isStrictlyPositive()) {
                    auto abs1 = l1.abs();
                    auto abs2 = r1.abs();
                    auto abs = abs1.sgt(abs2) ? abs1 : abs2;
                    APInt ll(abs);
                    ll.flipAllBits();
                    ++ll;
                    return makeRange(context, ll, abs);
                }
                else {
                    if (l2 == 0 || r2 == 0) {
                        return infRange();
                    }

                    SmallVector<APInt, 4> candidates;
                    bool ofFlags[4];
                    candidates.push_back(l1.sdiv_ov(l2, ofFlags[0]));
                    candidates.push_back(l1.sdiv_ov(r2, ofFlags[1]));
                    candidates.push_back(r1.sdiv_ov(l2, ofFlags[2]));
                    candidates.push_back(r1.sdiv_ov(r2, ofFlags[3]));
                    for (auto of:ofFlags) {
                        if (of) {
                            return infRange();
                        }
                    }
                    auto mx = candidates[0];
                    for (auto &xx : candidates) {
                        if (xx.sgt(mx)) {
                            mx = xx;
                        }
                    }
                    auto mn = candidates[0];
                    for (auto &xx : candidates) {
                        if (xx.slt(mn)) {
                            mn = xx;
                        }
                    }
                    return makeRange(context, mn, mx);
                }
            }
            else if (opcode == Instruction::UDiv) {
                if (l2 == 0 || r2 == 0) {
                    return infRange();
                }
                auto ll = r1.udiv(l2);
                auto rr = l1.udiv(r2);
                return makeRange(context, ll, rr);
            }
            else {
                // todo: fill in
                return infRange();
            }
        }
        else if (range1.isInfinity() || range2.isInfinity()) {
            RangeValue r;
            r.kind = PossibleRangeValues::infinity;
            return r;
        }
        else {
            RangeValue r;
            return r;
        }
    }

    RangeValue evaluateCast(llvm::CastInst &castOp, RangeState &state) const {
        auto *op = castOp.getOperand(0);
        auto value = getRangeFor(op, state);
        if (value.isConstant()) {
            auto &layout = castOp.getModule()->getDataLayout();
            if (!llvm::CastInst::castIsValid(castOp.getOpcode(), value.lvalue, castOp.getDestTy()) || 
                !llvm::CastInst::castIsValid(castOp.getOpcode(), value.rvalue, castOp.getDestTy())) {
                return infRange(); // Invalid cast
            }
            auto x = ConstantFoldCastOperand(castOp.getOpcode(), value.lvalue,
                                            castOp.getDestTy(), layout);
            auto y = ConstantFoldCastOperand(castOp.getOpcode(), value.rvalue,
                                            castOp.getDestTy(), layout);
            if (llvm::isa<llvm::ConstantExpr>(x) || llvm::isa<llvm::ConstantExpr>(y)) {
                return infRange(); // Cast produced a non-constant expression
            } else {
                auto *cix = dyn_cast<ConstantInt>(x);
                auto *ciy = dyn_cast<ConstantInt>(y);

                if (cix && ciy) {
                    // Valid constants
                    RangeValue r;
                    r.kind = PossibleRangeValues::constant;
                    r.lvalue = cix;
                    r.rvalue = ciy;
                    return r;
                } else {
                    // Cast failed to produce valid ConstantInt
                    return infRange();
                }
            }
        } else {
            RangeValue r;
            r.kind = value.kind;
            return r;
        }
    }

    void
    operator()(llvm::Value &i, RangeState &state) {
        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Processing instruction: " << i << "\n";);

        // If store => handle
        if (auto *st = dyn_cast<StoreInst>(&i)) {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Instruction is a StoreInst.\n";);
            handleStore(*st, state);
            return;
        }
        // If load => handle
        if (auto *ld = dyn_cast<LoadInst>(&i)) {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Instruction is a LoadInst.\n";);
            handleLoad(*ld, state);
            return;
        }

        // if recognized as malloc => record size
        {
            uint64_t sz = 0;
            if (isKnownMallocCall(&i, sz)) {
                // We do not directly store it into the state here;
                // usually it's stored to a variable. handleStore sees it.
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Malloc call recognized. Size: " << sz << "\n";);
            }
        }

        // Handle bitcast of malloc result to track derived pointers
        if (auto *castInst = dyn_cast<BitCastInst>(&i)) {
            llvm::Value *originalPtr = castInst->getOperand(0)->stripPointerCasts();
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Instruction is a BitCastInst. Original pointer: " << *originalPtr << "\n";);
            auto it = state.find(originalPtr);
            if (it != state.end() && it->second.isConstant()) {
                // unify bit widths to 64
                uint64_t allocSize = it->second.rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
                state[&i] = makeRange(castInst->getContext(),
                                      APInt(64, 0),
                                      APInt(64, allocSize - 1));
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Associated derived pointer with size: " << allocSize << "\n";);
            }
        }

        // Handle GetElementPtrInst (GEP)
        if (auto *gep = dyn_cast<GetElementPtrInst>(&i)) {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Instruction is a GetElementPtrInst.\n";);
            handleGEP(*gep, state);
            return;
        }

        if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(&i)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = constant;
            state[&i] = r;
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "ConstantInt found. Setting range to constant.\n";);
        }
        else if (auto *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&i)) {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "BinaryOperator found. Evaluating operation.\n";);
            state[binOp] = evaluateBinOP(*binOp, state);
        }
        else if (auto *castOp = llvm::dyn_cast<llvm::CastInst>(&i)) {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "CastInst found. Evaluating cast.\n";);
            state[castOp] = evaluateCast(*castOp, state);
        }
        else {
            state[&i].kind = PossibleRangeValues::infinity;
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Instruction needs further process or uninterested. Setting range to infinity at this moment to retain soundness.\n";);
        }
    }
private:
    void handleStore(StoreInst &SI, RangeState &state) const {
        llvm::Value *val = SI.getValueOperand();
        llvm::Value *ptr = SI.getPointerOperand();

        uint32_t bitWidth = 64;
        const Type *valType = val->getType();
        const IntegerType *intTy = dyn_cast<IntegerType>(valType);
        if (intTy) {
            bitWidth = intTy->getBitWidth();
        }

        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Handling StoreInst. Value: " << *val << ", Pointer: " << *ptr << "\n";);

        if (isLocalAllocaPointer(ptr)) {
            auto it = storeHappened.find(ptr);
            auto valRange = getRangeFor(val, state);

            if (it == storeHappened.end()) {
                storeHappened[ptr] = true;
                state[ptr] = valRange;
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "First store to pointer " << *ptr << ". Setting range.\n";);
            } else {
                state[ptr] = valRange;
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Subsequent store to pointer " << *ptr << ". Updating range.\n";);
            }

            // Propagate allocation size if val is a malloc or derived pointer
            uint64_t sz = 0;
            if (isKnownMallocCall(val, sz)) {
                // If sz == 0 => non-constant => treat as unknown => infinity
                if (sz == 0) {
                    state[ptr] = infRange();
                    UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Propagated unknown malloc size to stored pointer " << *ptr << "\n";);
                } else {
                    state[ptr] = makeRange(ptr->getContext(), APInt(bitWidth, 0), APInt(bitWidth, sz - 1));
                    UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Propagated malloc size " << sz << " to stored pointer " << *ptr << "\n";);
                }
            }
            else if (state.find(val) != state.end() && state[val].isConstant()) {
                uint64_t allocSize = state[val].rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
                state[ptr] = makeRange(ptr->getContext(), APInt(bitWidth, 0), APInt(bitWidth, allocSize - 1));
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Propagated malloc size " << allocSize << " to stored pointer " << *ptr << "\n";);
            }
        }
    }

    void handleLoad(LoadInst &LI, RangeState &state) const {
        llvm::Value *ptr = LI.getPointerOperand();
        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Handling LoadInst. Pointer: " << *ptr << "\n";);
        if (isLocalAllocaPointer(ptr)) {
            auto it = state.find(ptr);
            if (it != state.end()) {
                state[&LI] = it->second;
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Loaded value from pointer " << *ptr << " with range kind: " 
                            << static_cast<int>(it->second.kind) << "\n";);
                return;
            }
        }

        // Fallback: unknown or infinity
        state[&LI].kind = PossibleRangeValues::infinity;
        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Pointer not found or not a local alloca. Setting load range to infinity.\n";);
    }

    void handleGEP(GetElementPtrInst &gep, RangeState &state) const {
        llvm::Value *basePtr = gep.getPointerOperand();
        UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Handling GEP. Base pointer: " << *basePtr << "\n";);

        // Retrieve base pointer's range
        RangeValue baseRange = getRangeFor(basePtr, state);
        if (baseRange.isInfinity() || baseRange.isUnknown()) {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Base pointer range is infinity or unknown. Setting GEP range to infinity.\n";);
            state[&gep].kind = PossibleRangeValues::infinity;
            return;
        }

        // Handle multi-dimensional GEPs by iterating over all indices
        unsigned numIndices = gep.getNumIndices();
        APInt totalOffset(64, 0); // always 64-bit offset

        for (unsigned i = 0; i < numIndices; ++i) {
            llvm::Value *indexVal = gep.getOperand(i + 1); // Operand 0 is the base pointer
            RangeValue indexRange = getRangeFor(indexVal, state);

            if (indexRange.isInfinity() || indexRange.isUnknown()) {
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "GEP index range is infinity or unknown. Setting GEP range to infinity.\n";);
                state[&gep].kind = PossibleRangeValues::infinity;
                return;
            }

            // Handle constant indices
            if (indexRange.isConstant()) {
                // unify bit widths
                APInt idx = indexRange.lvalue->getValue().sextOrTrunc(64);
                int64_t index = idx.getSExtValue();
                const DataLayout &DL = gep.getModule()->getDataLayout();
                Type *elemType = gep.getResultElementType();
                uint64_t elemSize = DL.getTypeAllocSize(elemType);

                if (index < 0) {
                    UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "GEP index " << index << " is negative. Setting range to infinity.\n";);
                    state[&gep].kind = PossibleRangeValues::infinity;
                    return;
                }

                // Calculate the total offset in bytes
                APInt indexOffset = APInt(64, (uint64_t)index) * APInt(64, elemSize);
                totalOffset += indexOffset;

                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "GEP index " << index << " contributes " << elemSize 
                            << " bytes. Total offset now: " << totalOffset << " bytes.\n";);
            }
            else {
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "GEP index is not constant. Setting GEP range to infinity.\n";);
                state[&gep].kind = PossibleRangeValues::infinity;
                return;
            }
        }

        // Check if the total offset is within the base pointer's allocated size
        if (baseRange.isConstant()) {
            // unify bitwidth
            uint64_t allocSize = baseRange.rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
            uint64_t computedOffset = totalOffset.getZExtValue();

            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Computed total offset: " << computedOffset 
                        << " bytes. Allocated size: " << allocSize << " bytes\n";);

            if (computedOffset < allocSize) {
                // corrected Range: [0, allocSize - computedOffset - 1]
                if (allocSize <= computedOffset) {
                    UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Computed offset exceeds or equals allocated size. Setting range to infinity.\n";);
                    state[&gep].kind = PossibleRangeValues::infinity;
                    return;
                }
                uint64_t newMaxValue = allocSize - computedOffset - 1;
                APInt lower = APInt(64, 0);
                APInt upper = APInt(64, newMaxValue);
                RangeValue gepRange = makeRange(gep.getContext(), lower, upper);
                state[&gep] = gepRange;
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "GEP offset is within bounds. Setting range to [0, " << newMaxValue << "]\n";);
            }
            else {
                UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "GEP offset exceeds allocated size. Setting range to infinity.\n";);
                state[&gep].kind = PossibleRangeValues::infinity;
            }
        }
        else {
            UMS_DEBUG(DEBUG_SWITCH, llvm::errs() << "Base pointer does not have an associated allocation size. Setting GEP range to infinity.\n";);
            state[&gep].kind = PossibleRangeValues::infinity;
        }
    }
};

static std::set<BasicBlock *> unsafeBB;

void valueRangeAnalysis(Module *M, std::map<const UnifiedMemSafe::VariableMapKeyType *, 
                        UnifiedMemSafe::VariableInfo>heapSeqPointerSet, 
                        UnifiedMemSafe::AnalysisState TheState, 
                        std::set<const Instruction *> &oowResults,
                        pdg::PTAWrapper &PTA) {
    // I removed the print messages for cleanness in this pass
    // If you want to print, e.g., declaration and use sites, please refer to DataGuard Repository for the statements
    // auto *mainFunction = M->getFunction("main");
    auto *mainFunction = M->getFunction(EntryFunction.getValue());
    if (!mainFunction) {
       errs() << RED << "Unable to find " << EntryFunction.getValue() << " function for Value-Range Analysis! Skipping!\n" << NORMAL;
       return;
    }
    
    using Value    = RangeValue;
    using Transfer = RangeTransfer;
    using Meet     = RangeMeet;
    using Analysis = analysis::ForwardDataflowAnalysis<Value, Transfer, Meet>;
    Analysis analysis{*M, mainFunction};
    auto &results = analysis.computeForwardDataflow();

    if (DebugVR) {
        for (auto & [ctxt, contextResults] : results) {
            for (auto & [function, rangeStates] : contextResults) {
                for (auto &BB : *function) {
                    for (auto &I : BB) {
                        DEBUG_PRINT("Instruction: " << I);
                        DEBUG_PRINT("State:" << results[ctxt][function][&I].size());
                        analysis.printState(results[ctxt][function][&I]);
                    }
                }
            }
        }
    }

    std::map<UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapUnsafeSeqPointerSet;
    
    for (auto & [ctxt, contextResults] : results) {
        for (auto & [function, rangeStates] : contextResults) {
            for (auto &valueStatePair : rangeStates) {
                auto *inst = llvm::dyn_cast<llvm::GetElementPtrInst>(valueStatePair.first);
                if (!inst) {
                    // if (auto *inst = dyn_cast<Instruction>(valueStatePair.first)) {
                    //     DEBUG_PRINT("Skipping non-GEP instruction: " << *(valueStatePair.first));
                    //     analysis.printState(analysis::getIncomingState(rangeStates, *inst));
                    // }
                    continue;
                }
                DEBUG_PRINT("GEP Instruction(" << inst << "): " << *inst);
                if (heapSeqPointerSet.find(inst) != heapSeqPointerSet.end()){
                    DEBUG_PRINT("GEP in heapSeqPointerSet");
                    auto &state = analysis::getIncomingState(rangeStates, *inst);
                    Type *type = cast<PointerType>(
                            cast<GetElementPtrInst>(inst)->getPointerOperandType())->getElementType();
                    auto pointerTy = dyn_cast_or_null<PointerType>(type);
                    auto arrayTy = dyn_cast_or_null<ArrayType>(type);
                    auto structTy = dyn_cast_or_null<StructType>(type);

                    if(!arrayTy && !structTy){
                        if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                            // Check if vmktinfo is non-null
                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                if(!vmktinfo){
                                    // vmktinfo is NULL
                                    DEBUG_PRINT("vmktinfo is NULL; skipping analysis.");
                                    continue;
                                }
                                if (auto *gepInst = dyn_cast<llvm::GetElementPtrInst>(inst)) {
                                    // Check the number of operands in the GEP instruction
                                    auto index = (gepInst->getNumOperands() > 2) 
                                                ? gepInst->getOperand(2)  // Use the third operand if more than 2 operands
                                                : gepInst->getOperand(1); // Use the second operand otherwise
                                    DEBUG_PRINT("GEP index operand: " << *index);
                                    
                                    auto constant = dyn_cast<ConstantInt>(index);
                                    if (constant) {
                                        // If the offset is constant
                                        auto *sizeCI = dyn_cast<ConstantInt>(vmktinfo->size);
                                        if(!sizeCI) {
                                            // vmktinfo->size is not a ConstantInt
                                            DEBUG_PRINT("vmktinfo->size is not a ConstantInt. Skipping analysis.");
                                            continue;
                                        }
                                        int underlyingSize = sizeCI->getSExtValue();

                                        DEBUG_PRINT("Index is a constant: " << constant->getSExtValue()
                                                   << ", Underlying size: " << underlyingSize);
                                        if (!constant->isNegative() && underlyingSize > 0) {
                                            // Offset is within bounds, discard this case
                                            DEBUG_PRINT("Index is within valid range. Continuing.");
                                            continue;
                                        } else {
                                            DEBUG_PRINT("Index is out of valid range. Marking as unsafe: " << *constant << " > " << underlyingSize);
                                            // Offset is out of bounds, add to the set
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        }
                                    } else {
                                        DEBUG_PRINT("Index is not a constant. Marking as unsafe.");
                                        // If the index is not constant, add to the set
                                        heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                    }
                                }
                            }
                        }
                        continue;
                    }
                    else if(arrayTy){
                        auto size = arrayTy->getNumElements();
                        auto elmtTy = arrayTy->getElementType();
                        auto &layout = M->getDataLayout();
                        auto numBytes = layout.getTypeAllocSize(arrayTy);
                        auto elmtBytes = layout.getTypeAllocSize(elmtTy);
                        llvm::Value* index;
                        if(inst->getNumOperands() > 2)
                            index = inst->getOperand(2);
                        else {
                            index = inst->getOperand(1);
                        }
                        DEBUG_PRINT("Array GEP index operand: " << *index);
                        auto constant = dyn_cast<ConstantInt>(index);
                        if (constant) {
                            DEBUG_PRINT("Array index is a constant: " << constant->getSExtValue());
                            if (!constant->isNegative() && !constant->uge(size)) {
                                if (numBytes >= ((int64_t) constant->getValue().getLimitedValue() * elmtBytes)){
                                    DEBUG_PRINT("Array size in terms of number of elements: "<< numBytes/elmtBytes);
                                    DEBUG_PRINT("Array total size: "<< numBytes);
                                    DEBUG_PRINT("Array index within bounds. Safe access.");
                                }
                                else {
                                    DEBUG_PRINT("Array index multiplied by element size exceeds allocated bytes. Marking as unsafe.");
                                    if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            } else {
                                DEBUG_PRINT("Array index is negative or exceeds the size. Marking as unsafe.");
                                if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                        DEBUG_PRINT("Pointer marked as unsafe.");
                                    }
                                }
                            }
                        }
                        else {
                            auto &rangeValue = state[index];
                            // errs() << "Range Value: " << rangeValue.lvalue->getValue() << "\n";
                            // errs() << "Range Value: " << rangeValue.rvalue->getValue() << "\n";
                            if (rangeValue.isUnknown() ||
                                rangeValue.isInfinity() ||
                                !rangeValue.lvalue || !rangeValue.rvalue || 
                                rangeValue.lvalue->isNegative() ||
                                rangeValue.rvalue->uge(size)) {
                                if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                    }
                                }
                            }
                        }
                    }
                    
                    else if(structTy){
                        auto size = structTy->getNumElements();
                        auto &layout = M->getDataLayout();
                        auto numBytes = layout.getTypeAllocSize(structTy);
                        llvm::Value* index;
                        if(inst->getNumOperands() > 2)
                            index = inst->getOperand(2);
                        else {
                            index = inst->getOperand(1);
                        }
                        DEBUG_PRINT("Struct GEP index operand: " << *index);
                        
                        const llvm::StructLayout* structureLayout = layout.getStructLayout(structTy);
                        auto constant = dyn_cast<ConstantInt>(index);
                        if (constant) {
                            auto intIndex = (uint64_t)constant->getValue().getLimitedValue();
                            DEBUG_PRINT("Struct index is a constant: " << intIndex);
                            if(intIndex < size){
                                auto offset = structureLayout->getElementOffset(intIndex);
                                DEBUG_PRINT("Struct element offset: " << offset);
                                DEBUG_PRINT("Struct total size: " << numBytes);
                                if (!constant->isNegative() && !constant->uge(size)) {
                                    if (numBytes >= offset){
                                        DEBUG_PRINT("Struct index within bounds based on offset. Safe access.");
                                    }
                                    else{
                                        DEBUG_PRINT("Struct index offset exceeds allocated bytes. Marking as unsafe.");
                                        if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    } 
                                }  
                            }
                            else{
                                DEBUG_PRINT("Struct index exceeds number of elements. Marking as unsafe.");
                                if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                        DEBUG_PRINT("Pointer marked as unsafe.");
                                    }
                                }
                            }
                        }
                        else {
                            auto &rangeValue = state[index];
                            if (rangeValue.isUnknown() ||
                                rangeValue.isInfinity() ||
                                !rangeValue.lvalue || !rangeValue.rvalue ||
                                rangeValue.lvalue->isNegative() ||
                                rangeValue.rvalue->uge(size)) {
                                if (rangeValue.isInfinity() || rangeValue.isUnknown()) {
                                    if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    else{
                        // Additional processing can be added here.
                    }
                }           
            }
        }
    }

    std::set<const llvm::Value *> safeSeqPointerSet;
    for (auto heapPtr : heapSeqPointerSet) {
        if (!isa<GetElementPtrInst>(heapPtr.first)) {
            continue;
        }
        safeSeqPointerSet.insert(heapPtr.first);
    }

    if (EnableOOWAnalysis) {
        errs() << GREEN << "Before filtering out of window GEPs:\t" << DETAIL << heapUnsafeSeqPointerSet.size() << NORMAL << "\n";
        for (auto heapUnsafeSeqPointer = heapUnsafeSeqPointerSet.begin(); heapUnsafeSeqPointer != heapUnsafeSeqPointerSet.end();) {
            Instruction *gep = dyn_cast<Instruction>(heapUnsafeSeqPointer->first);
            if (oowResults.find(gep) != oowResults.end()) {
                errs() << RED << "Out of Window GEP: " << DETAIL << gep  << " - "  << *gep << NORMAL << "\n";
                heapUnsafeSeqPointer = heapUnsafeSeqPointerSet.erase(heapUnsafeSeqPointer);
            } else {
                ++heapUnsafeSeqPointer;
            }
        }
        errs() << GREEN << "After filtering out of window GEPs:\t" << DETAIL << heapUnsafeSeqPointerSet.size() << NORMAL << "\n";
    }

    // Using SFI along
    if (SFIOnly) {
        std::set<llvm::Value *> unsafeGEPSet;
        for (auto unsafeSeqPtr : heapUnsafeSeqPointerSet) {
            unsafeGEPSet.insert(unsafeSeqPtr.first);
        }
        tagOperationsForProtections(M, unsafeGEPSet, PTA);
    }

    // If we are getting diff, we need to remove whatever DG is reporting
    if (DiffOnly) {
        // 1. Going through the Module and collecting all unsafe GEPs reported by DG
        std::set<llvm::Value *> dgUnsafeGEPs;
        for (auto &F : *M) {
            for (auto &BB : F) {
                for (auto &I : BB) {
                    if (auto *call = dyn_cast<CallInst>(&I)) {
                        llvm::Value *calledVal = call->getCalledOperand();
                        if (auto *asmVal = llvm::dyn_cast<llvm::InlineAsm>(calledVal)) {
                            // Extract the asm string
                            std::string asmStr = asmVal->getAsmString();
                            if (asmStr == NORMAL_MAGIC_ASM_END) {
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

        tagOperationsForProtections(M, dgUnsafeGEPs, PTA);

        // If we use safe stack, any unsafe object put in unsafe region can be ignored, so we filter
        // out all the geps related to this object, but if we use baggy, we want to filter out all
        // the geps that is instrumented.
        if (UseBaggy) {
            // 2. Just remove
            for (auto heapUnsafeSeqPointer = heapUnsafeSeqPointerSet.begin(); heapUnsafeSeqPointer != heapUnsafeSeqPointerSet.end();) {
                if (dgUnsafeGEPs.find(heapUnsafeSeqPointer->first) != dgUnsafeGEPs.end()) {
                    heapUnsafeSeqPointer = heapUnsafeSeqPointerSet.erase(heapUnsafeSeqPointer);
                } else {
                    heapUnsafeSeqPointer++;
                }
            }
        } else {
            // 2. Collect all the memory objects that are accessed by these GEPs
            std::unordered_set<SVF::NodeID> dgUnsafeObjectSet;
            for (auto dgUnsafeGEP : dgUnsafeGEPs) {
                const GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(dgUnsafeGEP);
                if (gep) {
                    const llvm::Value *v = gep->getPointerOperand();
                    int ptsSize = PTA.insertUnsafePts(*v, dgUnsafeObjectSet);
                }
            }


            // 3. Remove any GEPs in heapUnsafeSeqPointerSet that access any of these memory objects
            for (auto heapUnsafeSeqPointer = heapUnsafeSeqPointerSet.begin(); heapUnsafeSeqPointer != heapUnsafeSeqPointerSet.end();) {
                const GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(heapUnsafeSeqPointer->first);
                if (gep) {
                    const llvm::Value *v = gep->getPointerOperand();
                    std::unordered_set<SVF::NodeID> gepPtsSet;
                    int ptsSize = PTA.insertUnsafePts(*v, gepPtsSet);
                    bool overlap = false;
                    for (auto pt : gepPtsSet) {
                        if (dgUnsafeObjectSet.find(pt) != dgUnsafeObjectSet.end()) {
                            overlap = true;
                            break;
                        }
                    }
                    if (overlap) {
                        heapUnsafeSeqPointer = heapUnsafeSeqPointerSet.erase(heapUnsafeSeqPointer);
                    } else {
                        ++heapUnsafeSeqPointer;
                    }
                } else {
                    ++heapUnsafeSeqPointer;
                }
            }
        }

        errs() << GREEN << "# of GEPs protected by SLH:\t\t" << DETAIL << heapUnsafeSeqPointerSet.size()<< NORMAL << "\n"; 
    }

    errs() << GREEN << "Unsafe Seq Pointer After Value Range Analysis:\t\t" << DETAIL << heapUnsafeSeqPointerSet.size()<< NORMAL << "\n"; 
    errs() << "++++++++++++++++\n";
    for (auto heapUnsafeSeqPointer : heapUnsafeSeqPointerSet) {
        safeSeqPointerSet.erase(heapUnsafeSeqPointer.first);
        
        Instruction *gep = dyn_cast<Instruction>(heapUnsafeSeqPointer.first);
        unsafeBB.insert(gep->getParent());

        auto nextInst = gep->getNextNode();

        if (auto *call = dyn_cast<CallBase>(nextInst)) {
            if (InlineAsm *dummyAsm = dyn_cast<InlineAsm>(call->getCalledOperand())) {
                std::string asmString = dummyAsm->getAsmString();
                if (asmString.find(NORMAL_MAGIC_ASM_END) != std::string::npos ||
                    asmString.find(MAGIC_ASM_END) != std::string::npos) {
                    continue;
                }
            }
        }

        LLVMContext &context = gep->getParent()->getParent()->getContext();

        FunctionType *asmType = FunctionType::get(Type::getVoidTy(context), false);

        InlineAsm *asmBefore = nullptr;
        if (UsePC) {
            asmBefore = InlineAsm::get(asmType, NORMAL_MAGIC_ASM_BEGIN, "", true);
        } else {
            asmBefore = InlineAsm::get(asmType, MAGIC_ASM_BEGIN, "", true);
        }
        // Create the inline assembly instruction using Create
        Instruction *asmInstBefore = CallInst::Create(asmBefore, {}, "", gep);

        
        InlineAsm *asmAfter = nullptr;
        if (UsePC) {
            asmAfter = InlineAsm::get(asmType, NORMAL_MAGIC_ASM_END, "", true);
        } else {
            asmAfter = InlineAsm::get(asmType, MAGIC_ASM_END, "", true);
        }
        Instruction *asmInstAfter = CallInst::Create(asmAfter, {}, "", &*nextInst);

        errs() << RED << "Unsafe Seq Pointer: " << DETAIL << *(heapUnsafeSeqPointer.first) << NORMAL << "\n";
        const DILocation *loc = gep->getDebugLoc();
        if (loc) {
            errs() << "Source: " << loc->getFilename() << " line "
                << std::to_string(loc->getLine()) << "\n";
        } else {
            errs() << "Debug information missing, no trace back to source.\n";
        }
    }
    errs() << "++++++++++++++++\n\n";

    if (DebugVR) {
        errs() << GREEN << "Safe Seq Pointer After Value Range Analysis:\t\t" << DETAIL << safeSeqPointerSet.size() << NORMAL << "\n";
        errs() << GREEN << "+++++++++++++++++++++Safe Seq Pointer begin++++++++++++++++++++\n";
        for (auto safePtr : safeSeqPointerSet) {
            errs() << GREEN << "Safe Seq Pointer: " << DETAIL << *safePtr << NORMAL << "\n";
        }
        errs() << GREEN << "+++++++++++++++++++++Safe Seq Pointer end++++++++++++++++++++\n";
    }

    errs() << GREEN << "Unsafe Basic Block Size:\t\t" << DETAIL << unsafeBB.size() << NORMAL << "\n";

    std::unordered_set<SVF::NodeID> unsafeObjectSet;
    for (auto heapUnsafeSeqPointer : heapUnsafeSeqPointerSet) {
        GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(heapUnsafeSeqPointer.first);
        if (gep) {
            const llvm::Value *v = gep->getPointerOperand();
            int ptsSize = PTA.insertUnsafePts(*v, unsafeObjectSet);
            errs() << "Base object newly added for " << gep->getParent()->getParent()->getName() << ":" << *gep << ": " << ptsSize << "\n";
            for (auto pt : unsafeObjectSet) {
                errs() << pt << " ";
            }
            errs() << "\n";
        }
    }

    int heapSize = 0;
    int stackSize = 0;
    errs() << GREEN << "+++++++++++++++++++++Unsafe Object start++++++++++++++++++++\n";
    for (auto unsafeObj : unsafeObjectSet) {
        if (PTA.isHeapObject(unsafeObj)) {
            heapSize++;
            errs() << "Unsafe Object (Heap): " << DETAIL << unsafeObj << NORMAL << "\n";
        } else if (PTA.isStackObject(unsafeObj)) {
            stackSize++;
            errs() << "Unsafe Object (Stack): " << DETAIL << unsafeObj << NORMAL << "\n";
        } else {
            errs() << "Unsafe Object (Other): " << DETAIL << unsafeObj << NORMAL << "\n";
        }
    }
    errs() << GREEN << "+++++++++++++++++++++Unsafe Object end++++++++++++++++++++\n";
    errs() << GREEN << "Unsafe Object After Value Range Analysis:\t\t" << DETAIL << unsafeObjectSet.size() << NORMAL << "\n";
    errs() << GREEN << "Unsafe Heap Object:\t" << DETAIL << heapSize << NORMAL << "\n";
    errs() << GREEN << "Unsafe Stack Object:\t" << DETAIL << stackSize << NORMAL << "\n";

    errs() << GREEN << "Total Objects:\t" << DETAIL << PTA.getNumOfObjects() << NORMAL << "\n";

    /*for (const auto &pair : heapUnsafeSeqPointerSet) {
        const llvm::Value *key = pair.first;

        // Use llvm::dyn_cast to cast the key to an Instruction
        if (const llvm::Instruction *instruction = llvm::dyn_cast<llvm::Instruction>(key)) {
            // Print the instruction using LLVM's print method
            instruction->print(llvm::outs());
            llvm::outs() << "\n";
        } else {
            std::cerr << "Key cannot be cast to LLVM Instruction." << std::endl;
        }
    }
    */
}

void tagOperationsForProtections(Module *M, std::set<llvm::Value *> &unsafeSeqPointerSet, pdg::PTAWrapper &PTA) {
    // 1. mark unsafe gep for baggy and collect unsafe objects
    std::unordered_set<SVF::NodeID> dgUnsafeObjectSet;
    for (auto unsafeGEP : unsafeSeqPointerSet) {
        auto *gep = dyn_cast<GetElementPtrInst>(unsafeGEP);
        if (gep) {
            gep->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
            const llvm::Value *v = gep->getPointerOperand();
            int ptsSize = PTA.insertUnsafePts(*v, dgUnsafeObjectSet);
        }
    }

    errs() << GREEN << "# of GEPs protected by SFI:\t\t" << DETAIL << unsafeSeqPointerSet.size()<< NORMAL << "\n"; 

    // 2 collect allocas (also mallocs) that are associated with unsafe objects.
    std::set<const CallBase *> unsafeMallocSet;
    std::set<const AllocaInst*> unsafeAllocaSet;
    std::set<const GlobalVariable*> unsafeGlobalSet;
    for (auto unsafeObj : dgUnsafeObjectSet) {
        if (PTA.isStackObject(unsafeObj)) {
            DEBUG_PRINT("unsafe stack Obj:" << unsafeObj);
            const AllocaInst *alloca = PTA.getAlloca(unsafeObj);
            if (alloca) {
                unsafeAllocaSet.insert(alloca);
            }
        } else if (PTA.isHeapObject(unsafeObj)) {
            DEBUG_PRINT("unsafe heap Obj:" << unsafeObj);
            const CallBase *malloc = PTA.getMalloc(unsafeObj);
            if (malloc) {
                unsafeMallocSet.insert(malloc);
            }
        } else if (PTA.isGlobalObject(unsafeObj)) {
            DEBUG_PRINT("unsafe global Obj:" << unsafeObj);
            const GlobalVariable *global = PTA.getGlobal(unsafeObj);
            if (global) {
                unsafeGlobalSet.insert(global);
            }
        }
    }

    // 3. mark the allocas, mallocs and globals for safestack and deltapointers
    for (const AllocaInst* alloca : unsafeAllocaSet) {
        auto nonConstAlloca = const_cast<AllocaInst*>(alloca);
        nonConstAlloca->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
    }
    for (const CallBase* malloc : unsafeMallocSet) {
        auto nonConstMalloc = const_cast<CallBase*>(malloc);
        nonConstMalloc->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
    }
    for (const GlobalVariable* global : unsafeGlobalSet) {
        auto nonConstGlobal = const_cast<GlobalVariable*>(global);
        nonConstGlobal->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
    }


    // 4. find places that need masking for Delta pointers
    for (auto &F : *M) {
        for (auto &BB : F) {
            for (auto &I : BB) {
                if (auto *call = dyn_cast<CallBase>(&I)) {
                    auto *func = call->getCalledFunction();
                    if (!func) {
                        // TODO
                        continue;
                    }
                } else if (auto *load = dyn_cast<LoadInst>(&I)) {
                    if (PTA.isPointToUnsafeObjects(dgUnsafeObjectSet, *load->getPointerOperand())) {
                        load->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
                    }
                } else if (auto *store = dyn_cast<StoreInst>(&I)) {
                    if (PTA.isPointToUnsafeObjects(dgUnsafeObjectSet, *store->getPointerOperand())) {
                        store->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
                    }
                } else if (auto *gep = dyn_cast<GetElementPtrInst>(&I)) {
                    if (PTA.isPointToUnsafeObjects(dgUnsafeObjectSet, *gep->getPointerOperand())) {
                        if (unsafeSeqPointerSet.find(gep) == unsafeSeqPointerSet.end()) {
                            bool onlyUsedInLoadStore = false;
                            for (auto user : gep->users()) {
                                if (isa<LoadInst>(user)) {
                                    onlyUsedInLoadStore = true;
                                } else if (isa<StoreInst>(user) && user->getOperand(1) == gep) {
                                    onlyUsedInLoadStore = true;
                                } else {
                                    onlyUsedInLoadStore = false;
                                    break;
                                }
                            }
                            if (!onlyUsedInLoadStore) {
                                gep->setMetadata("dualguard.unsafe.dponly", MDNode::get(M->getContext(), {}));
                            }
                        }
                    }
                } 
                else if (auto *cmp = dyn_cast<CmpInst>(&I)) {
                    auto op1 = cmp->getOperand(0);
                    if (!op1->getType()->isPointerTy())
                        continue;

                    auto op2 = cmp->getOperand(1);
                    assert(op2->getType()->isPointerTy());

                    if (PTA.isPointToUnsafeObjects(dgUnsafeObjectSet, *op1) || PTA.isPointToUnsafeObjects(dgUnsafeObjectSet, *op2)) {
                        cmp->setMetadata("dualguard.unsafe", MDNode::get(M->getContext(), {}));
                    }
                }
            }
        }
    }
}