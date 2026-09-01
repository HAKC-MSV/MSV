#ifndef _PTAWRAPPER_H_
#define _PTAWRAPPER_H_
#include "LLVMEssentials.hh"
//#include "SVF-FE/PAGBuilder.h"
#include "WPA/Andersen.h"
#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "SVFIR/SVFModule.h"
//#include "SVF-FE/LLVMUtil.h"


namespace pdg
{
  class PTAWrapper final
  {
  public:
    PTAWrapper() = default;
    PTAWrapper(const PTAWrapper &) = delete;
    PTAWrapper(PTAWrapper &&) = delete;
    PTAWrapper &operator=(const PTAWrapper &) = delete;
    PTAWrapper &operator=(PTAWrapper &&) = delete;
    static PTAWrapper &getInstance()
    {
      static PTAWrapper ptaw{};
      return ptaw;
    }
    void setupPTA(llvm::Module &M);
    bool hasPTASetup() { return (_ander_pta != nullptr); }
    SVF::AliasResult queryAlias(llvm::Value &v1, llvm::Value &v2);
    int getSizeForValue(const llvm::Value &v, const llvm::DataLayout *CurrentDL);
    const SVF::PointsTo& getPts(const llvm::Value &v);
    void getExpandedFIPts(const llvm::Value &inst, SVF::PointsTo& expandedPts);
    int insertUnsafePts(const llvm::Value &v, std::unordered_set<SVF::NodeID> &unsafeObjSet);
    bool isHeapObject(SVF::NodeID id);
    bool isStackObject(SVF::NodeID id);
    bool isGlobalObject(SVF::NodeID id);
    int getNumOfObjects();
    SVF::NodeID getBaseObjectId(SVF::NodeID);
    const llvm::AllocaInst *getAlloca(SVF::NodeID id);
    const llvm::CallBase *getMalloc(SVF::NodeID id);
    const llvm::GlobalVariable *getGlobal(SVF::NodeID id);
    const llvm::Value *getLLVMValue(SVF::NodeID id);
    bool hasValueNode(const llvm::Value &v);
    SVF::NodeID getValueNode(const llvm::Value &v);
    void printPts(const SVF::PointsTo& pts);

    bool isPointToUnsafeObjects(std::unordered_set<SVF::NodeID> &unsafeObjSet, const llvm::Value &v);
    //SVF::PAG* getPAG();
    SVF::AndersenWaveDiff *_ander_pta;
  };
} 

#endif
