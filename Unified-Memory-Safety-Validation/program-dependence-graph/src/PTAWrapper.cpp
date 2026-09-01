#include "PTAWrapper.hh"

using namespace llvm;
using namespace SVF;

void pdg::PTAWrapper::setupPTA(Module &M)
{
  SVFModule *module = LLVMModuleSet::buildSVFModule(M);
  SVFIRBuilder *builder = new SVFIRBuilder(module);
  PAG *pag = builder->build();
  _ander_pta = AndersenWaveDiff::createAndersenWaveDiff(pag);
}

SVF::AliasResult pdg::PTAWrapper::queryAlias(Value &v1, Value &v2)
{
  assert(_ander_pta != nullptr && "cannot obtain ander pointer analysis!\n");
  SVFValue *svfV1 = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&v1);
  SVFValue *svfV2 = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&v2);
  return _ander_pta->alias(svfV1, svfV2);
}

int pdg::PTAWrapper::getSizeForValue(const llvm::Value &v, const DataLayout *CurrentDL) {
  PAG* pag = _ander_pta->getPAG();
  SVF::PointsTo expandedPts;
  getExpandedFIPts(v, expandedPts);
  // const SVF::PointsTo& pts = getPts(v);
  // printPts(expandedPts);

  const SVFType *finalType = nullptr;
  for (SVF::PointsTo::iterator it = expandedPts.begin(), eit = expandedPts.end(); it != eit;
                ++it) {
    PAGNode* pagNode = pag->getGNode(*it);
    NodeID id = *it;
    if (SVF::ObjVar *obj = dyn_cast<SVF::ObjVar>(pagNode)) {
      if (finalType == nullptr) {
        finalType = obj->getMemObj()->getType();
      } else {
        if (finalType != obj->getMemObj()->getType()) {
          // Different types, cannot determine size
          return -1;
        }
      }
    }
  }

  int finalSize = -1;

  if (finalType != nullptr) {
    // errs() << "Final type for " << v.getName() << ": " << *finalType << "\n";
    if (finalType->isPointerTy())
      finalType = ((SVFPointerType *)finalType)->getPtrElementType();
    if (const SVFArrayType *arrT = dyn_cast<SVFArrayType>(finalType)){
      int arraysize = finalType->getTypeInfo()->getNumOfFlattenElements();
      int totalsize = arrT->getTypeOfElement()->getByteSize();
      finalSize = arraysize * totalsize;
    }
    else if (const SVFStructType *stT = dyn_cast<SVFStructType>(finalType)){
      // errs() << "Struct name: " << stT->getName() << "\n";
      finalSize = finalType->getByteSize();
    }
  }
  return finalSize;
}

int pdg::PTAWrapper::insertUnsafePts(const llvm::Value &v, std::unordered_set<SVF::NodeID> &unsafeObjSet) {
  PAG* pag = _ander_pta->getPAG();
  int sizeBefore = unsafeObjSet.size();
  SVF::PointsTo pts;
  getExpandedFIPts(v, pts);
  for (SVF::PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit;
                ++it) {
    NodeID id = *it;
    unsafeObjSet.insert(pag->getBaseObj(id)->getId());
  }
  return unsafeObjSet.size() - sizeBefore;
}

const SVF::PointsTo& pdg::PTAWrapper::getPts(const llvm::Value &v) {
  PAG* pag = _ander_pta->getPAG();
  SVFValue *svfV = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&v);
  PAGNode* pagNode = pag->getGNode(pag->getValueNode(svfV));
  const SVF::PointsTo& pts = _ander_pta->getPts(pagNode->getId());
  return pts;
}

void pdg::PTAWrapper::getExpandedFIPts(const Value &inst, SVF::PointsTo& expandedPts) {
  const SVF::PointsTo& pts = getPts(inst);
  _ander_pta->expandFIObjs(pts, expandedPts);

}

bool pdg::PTAWrapper::isHeapObject(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);
  ObjVar *objNode = dyn_cast<ObjVar>(node);
  assert(objNode != nullptr && "Not an object node!\n");
  return objNode->getMemObj()->isHeap();
}

bool pdg::PTAWrapper::isStackObject(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);
  ObjVar *objNode = dyn_cast<ObjVar>(node);
  assert(objNode != nullptr && "Not an object node!\n");
  return objNode->getMemObj()->isStack();
}

bool pdg::PTAWrapper::isGlobalObject(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);
  ObjVar *objNode = dyn_cast<ObjVar>(node);
  assert(objNode != nullptr && "Not an object node!\n");
  return objNode->getMemObj()->isGlobalObj();
}

int pdg::PTAWrapper::getNumOfObjects() {
  PAG* pag = _ander_pta->getPAG();
  int num = 0;
  for (auto node = pag->begin(); node != pag->end(); node++) {
    if (isa<FIObjVar>(node->second)) {
      num++;
    }
  }
  return num;
}

SVF::NodeID pdg::PTAWrapper::getBaseObjectId(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  SVF::NodeID base = pag->getBaseObj(id)->getId();
  return base;
}

const llvm::AllocaInst *pdg::PTAWrapper::getAlloca(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);
  
  const llvm::Value *val = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(node->getValue());
  if (const llvm::AllocaInst *alloca = dyn_cast<llvm::AllocaInst>(val)) {
    return alloca;
  }
  assert(isa<llvm::AllocaInst>(val) && "Not an Alloca!\n");
  return nullptr;
}

const llvm::CallBase *pdg::PTAWrapper::getMalloc(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);

  if (isa<DummyObjVar>(node))
    return nullptr;
  
  const llvm::Value *val = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(node->getValue());
  if (const llvm::CallBase *call = dyn_cast<llvm::CallBase>(val)) {
      return call;
  }
  errs() << "Something is not right, check\n";
  return nullptr;
}

const llvm::GlobalVariable *pdg::PTAWrapper::getGlobal(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);
  const llvm::Value *val = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(node->getValue());
  if (const llvm::GlobalVariable *GV = dyn_cast<llvm::GlobalVariable>(val)) {
      return GV;
  }
  errs() << "Something is not right, check\n";
  return nullptr;
}

const llvm::Value *pdg::PTAWrapper::getLLVMValue(SVF::NodeID id) {
  PAG* pag = _ander_pta->getPAG();
  PAGNode *node = pag->getGNode(id);

  if (!node->hasValue())
    return nullptr;

  const llvm::Value *val = LLVMModuleSet::getLLVMModuleSet()->getLLVMValue(node->getValue());
  return val;
}

bool pdg::PTAWrapper::hasValueNode(const llvm::Value &v) {
  PAG* pag = _ander_pta->getPAG();
  if (!LLVMModuleSet::getLLVMModuleSet()->hasSVFValue(&v)) {
    return false;
  }
  SVFValue *svfV = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&v);
  return pag->hasValueNode(svfV);
}

SVF::NodeID pdg::PTAWrapper::getValueNode(const llvm::Value &v) {
  PAG* pag = _ander_pta->getPAG();
  SVFValue *svfV = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(&v);
  return pag->getValueNode(svfV);
}

bool pdg::PTAWrapper::isPointToUnsafeObjects(std::unordered_set<SVF::NodeID> &unsafeObjSet, const llvm::Value &v) {
  PAG* pag = _ander_pta->getPAG(); 
  SVF::PointsTo expandedPts;
  getExpandedFIPts(v, expandedPts);

  for (SVF::PointsTo::iterator it = expandedPts.begin(), eit = expandedPts.end(); it != eit;
                ++it) {
    PAGNode *node = pag->getGNode(*it);
    if (auto *gepNode = dyn_cast<GepObjVar>(node)) {
      expandedPts.set(gepNode->getBaseNode());
    }
  }

  // if (expandedPts.test(pag->getNullPtr())) {
  //   errs() << "Null pointer found\n";
  //   return true;
  // }

  for (SVF::PointsTo::iterator it = expandedPts.begin(), eit = expandedPts.end(); it != eit;
                ++it) {
    NodeID id = *it;
    if (unsafeObjSet.find(id) != unsafeObjSet.end()) {
      return true;
    }
  }
  return false;
}

void pdg::PTAWrapper::printPts(const SVF::PointsTo& pts) {
  std::unordered_set<SVF::NodeID> baseNodes;
  for (SVF::PointsTo::iterator it = pts.begin(), eit = pts.end(); it != eit;
                ++it) {
    baseNodes.insert(getBaseObjectId(*it));
  }
  for (NodeID id : baseNodes) {
    if (isHeapObject(id)) {
      errs() << "Heap object: " << id << *getMalloc(id) << "\n";
    } else if (isStackObject(id)) {
      errs() << "Stack object: " << id << *getAlloca(id) << "\n";
    } else if (isGlobalObject(id)) {
      errs() << "Global object: " << id << *getGlobal(id) << "\n";
    } else {
      errs() << "Unknown object type: " << id << "\n";
    }
  }
  errs() << "\n";
}