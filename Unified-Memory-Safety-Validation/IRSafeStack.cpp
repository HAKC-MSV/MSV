#include <llvm/Pass.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/Attributes.h>

using namespace llvm;

namespace {
struct IRSafeStack : public FunctionPass {
  static char ID;
  IRSafeStack() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if (F.isDeclaration())
      return false;

    // Add the safestack attribute to the function
    F.addFnAttr(Attribute::SafeStack);
    return true;
  }
};
} // namespace

char IRSafeStack::ID = 0;
static RegisterPass<IRSafeStack> X("ir-safestack",
                                   "Add safestack attribute to all functions",
                                   false, false);
