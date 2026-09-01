#include "DataDependencyGraph.hh"

char pdg::DataDependencyGraph::ID = 0;

using namespace llvm;

bool pdg::DataDependencyGraph::runOnModule(Module &M)
{
  // setup SVF 
  ProgramGraph &g = ProgramGraph::getInstance();
  PTAWrapper &ptaw = PTAWrapper::getInstance();
  if (!g.isBuild())
  {
    g.build(M);
    errs() << "Building\n";
    g.bindDITypeToNodes(M);
  }

  if (!ptaw.hasPTASetup())
    ptaw.setupPTA(M);


  std::chrono::milliseconds defuse = std::chrono::milliseconds::zero();
  std::chrono::milliseconds raw = std::chrono::milliseconds::zero();
  std::chrono::milliseconds alias = std::chrono::milliseconds::zero();

  std::chrono::_V2::system_clock::time_point t1;
  std::chrono::_V2::system_clock::time_point t2;
  std::chrono::_V2::system_clock::time_point t3;
  std::chrono::_V2::system_clock::time_point t4;

  for (auto &F : M)
  {
    if (F.isDeclaration() || F.empty())
      continue;
    errs() << "PDG: " << F.getName() << "\n";
    _mem_dep_res = &getAnalysis<MemoryDependenceWrapperPass>(F).getMemDep();

    std::unordered_map<int, std::set<Instruction*>> obj_to_instset_map;

    for (auto inst_iter = inst_begin(F); inst_iter != inst_end(F); inst_iter++)
    {
      // errs() << F.getName() << ": " << *inst_iter << "\n";
      t1 = std::chrono::high_resolution_clock::now();
      addDefUseEdges(*inst_iter);
      t2 = std::chrono::high_resolution_clock::now();
      defuse += std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1);
      addRAWEdges(*inst_iter);
      t3 = std::chrono::high_resolution_clock::now();
      raw += std::chrono::duration_cast<std::chrono::milliseconds>(t3 - t2);

      SVF::PointsTo expandedPts;
      ptaw.getExpandedFIPts(*inst_iter, expandedPts);
      for (auto it = expandedPts.begin(), eit = expandedPts.end(); it != eit; ++it) {
        if (obj_to_instset_map.find(*it) == obj_to_instset_map.end()) {
          obj_to_instset_map[*it] = std::set<Instruction*>();
        }
        obj_to_instset_map[*it].insert(&*inst_iter);
      }

      // inefficient implementation
      addAliasEdges(*inst_iter);
    }

    std::set<std::set<Instruction*>> unique_alias_inst_set;
    for (auto it = obj_to_instset_map.begin(), eit = obj_to_instset_map.end(); it != eit; ++it) {
      
      if (unique_alias_inst_set.find(it->second) != unique_alias_inst_set.end())
        continue;
      bool is_subset = false;
      for (auto iter = unique_alias_inst_set.begin(); iter != unique_alias_inst_set.end(); iter++) {
        if (std::includes(iter->begin(), iter->end(), it->second.begin(), it->second.end())) {
          is_subset = true;
          break;
        }

        if (std::includes(it->second.begin(), it->second.end(), iter->begin(), iter->end())) {
          unique_alias_inst_set.erase(iter);
          break;
        }
      }
      if (is_subset)
        continue;
      unique_alias_inst_set.insert(it->second);
    }

    errs() << "Unique alias set size: " << unique_alias_inst_set.size() << "\n";

    for (auto it = unique_alias_inst_set.begin(), eit = unique_alias_inst_set.end(); it != eit; ++it) {
      auto inst_set = *it;
      for (auto iter1 = inst_set.begin(); iter1 != inst_set.end(); iter1++) {
        for (auto iter2 = std::next(iter1); iter2 != inst_set.end(); iter2++) {
          Node* src = g.getNode(**iter1);
          Node* dst = g.getNode(**iter2);
          if (src == nullptr || dst == nullptr)
            continue;
          if (!isa<BitCastInst>(*iter1) && !isa<BitCastInst>(*iter2))
          {
            if ((*iter1)->getType() != (*iter2)->getType())
              continue;
          }
          src->addNeighbor(*dst, EdgeType::DATA_ALIAS);
          dst->addNeighbor(*src, EdgeType::DATA_ALIAS);
        }
      }
    }
    t4 = std::chrono::high_resolution_clock::now();
    alias += std::chrono::duration_cast<std::chrono::milliseconds>(t4 - t3);
  }
  errs() << "defuse: " << std::chrono::duration_cast<std::chrono::milliseconds>(defuse).count() << "\n";
  errs() << "raw: " << std::chrono::duration_cast<std::chrono::milliseconds>(raw).count() << "\n";
  errs() << "alias: " << std::chrono::duration_cast<std::chrono::milliseconds>(alias).count() << "\n";
  return false;
}


void pdg::DataDependencyGraph::addAliasEdges(Instruction &inst)
{
  ProgramGraph &g = ProgramGraph::getInstance();
  PTAWrapper &ptaw = PTAWrapper::getInstance();
  Function* func = inst.getFunction();
  for (auto inst_iter = inst_begin(func); inst_iter != inst_end(func); inst_iter++)
  {
    if (&inst == &*inst_iter)
      continue;
    if (!inst.getType()->isPointerTy())
      continue;
    // auto anders_aa_result = ptaw.queryAlias(inst, *inst_iter);
    auto alias_result = queryAliasUnderApproximate(inst, *inst_iter);
    if (alias_result != SVF::NoAlias)
    {
      Node* src = g.getNode(inst);
      Node* dst = g.getNode(*inst_iter);
      if (src == nullptr || dst == nullptr)
        continue;
      // use type info to eliminate dubious gep
      if (!isa<BitCastInst>(*inst_iter) && !isa<BitCastInst>(&inst))
      {
        if (inst.getType() != inst_iter->getType())
          continue;
      }
      src->addNeighbor(*dst, EdgeType::DATA_ALIAS);
      dst->addNeighbor(*src, EdgeType::DATA_ALIAS);
    }
  }
}

void pdg::DataDependencyGraph::addDefUseEdges(Instruction &inst)
{
  ProgramGraph &g = ProgramGraph::getInstance();
  for (auto user : inst.users())
  {
    Node *src = g.getNode(inst);
    Node *dst = g.getNode(*user);
    if (src == nullptr || dst == nullptr)
      continue;
    src->addNeighbor(*dst, EdgeType::DATA_DEF_USE);
  }
}

void pdg::DataDependencyGraph::addDefUseEdgesForGlobalVars(Module &M)
{
  
}

void pdg::DataDependencyGraph::addRAWEdges(Instruction &inst)
{
  if (!isa<LoadInst>(&inst))
    return;

  ProgramGraph &g = ProgramGraph::getInstance();
  auto dep_res = _mem_dep_res->getDependency(&inst);
  auto dep_inst = dep_res.getInst();

  if (!dep_inst)
    return;
  if (!isa<StoreInst>(dep_inst))
    return;

  Node *src = g.getNode(inst);
  Node *dst = g.getNode(*dep_inst);
  if (src == nullptr || dst == nullptr)
    return;
  dst->addNeighbor(*src, EdgeType::DATA_RAW);
}

SVF::AliasResult pdg::DataDependencyGraph::queryAliasUnderApproximate(Value &v1, Value &v2)
{
  if (!v1.getType()->isPointerTy() || !v2.getType()->isPointerTy())
    return SVF::NoAlias;
  // check bit cast
  if (BitCastInst *bci = dyn_cast<BitCastInst>(&v1))
  {
    if (bci->getOperand(0) == &v2)
      return SVF::MustAlias;
  }
  // handle load instruction  
  if (LoadInst* li = dyn_cast<LoadInst>(&v1))
  {
    auto load_addr = li->getPointerOperand();
    for (auto user : load_addr->users())
    {
      if (isa<LoadInst>(user))
      {
        if (user == &v2)
          return SVF::MustAlias;
      }
      if (StoreInst *si = dyn_cast<StoreInst>(user))
      {
        if (si->getPointerOperand() == load_addr)
        {
          if (si->getValueOperand() == &v2)
            return SVF::MustAlias;
        }
      }
    }
  }

  // handle gep
  if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&v1))
  {
    if (gep->getPointerOperand() == &v2 && gep->hasAllZeroIndices())
      return SVF::MustAlias;
  }
  return SVF::NoAlias;
}

void pdg::DataDependencyGraph::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<MemoryDependenceWrapperPass>();
  AU.setPreservesAll();
}

static RegisterPass<pdg::DataDependencyGraph>
    DDG("ddg", "Data Dependency Graph Construction", false, true);
