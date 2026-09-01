#include "PDGNode.hh"

using namespace llvm;

void pdg::Node::addNeighbor(Node &neighbor, EdgeType edge_type)
{
  Edge e(this, &neighbor, edge_type);
  addOutEdge(e);
  _out_neighbors.insert(&neighbor);
  _out_neighbors_with_edge_type[static_cast<int>(edge_type)].insert(&neighbor);
  neighbor.addInEdge(e);
  neighbor._in_neighbors.insert(this);
  neighbor._in_neighbors_with_edge_type[static_cast<int>(edge_type)].insert(this);
}

std::set<pdg::Node *> &pdg::Node::getInNeighbors()
{
  return _in_neighbors;
}

std::set<pdg::Node *> &pdg::Node::getInNeighborsWithDepType(pdg::EdgeType edge_type)
{
  return _in_neighbors_with_edge_type[static_cast<int>(edge_type)];
}

std::set<pdg::Node *> &pdg::Node::getOutNeighbors()
{
  return _out_neighbors;
}

std::set<pdg::Node *> &pdg::Node::getOutNeighborsWithDepType(pdg::EdgeType edge_type)
{
  return _out_neighbors_with_edge_type[static_cast<int>(edge_type)];
}

bool pdg::Node::hasInNeighborWithEdgeType(Node &n, EdgeType edge_type)
{
  return _in_edge_set.find(Edge(this, &n, edge_type)) != _in_edge_set.end();
}

bool pdg::Node::hasOutNeighborWithEdgeType(Node &n, EdgeType edge_type)
{
  return _out_edge_set.find(Edge(this, &n, edge_type)) != _out_edge_set.end();
}

std::set<pdg::Node *> &pdg::Node::getNeighborsWithDepType(std::set<pdg::EdgeType> edge_types)
{
  std::set<Node *> ret;
  for (auto edge : _in_edge_set)
  {
    if (edge_types.find(edge.getEdgeType()) != edge_types.end())
      ret.insert(edge.getSrcNode());
  }

  for (auto edge : _out_edge_set)
  {
    if (edge_types.find(edge.getEdgeType()) != edge_types.end())
      ret.insert(edge.getDstNode());
  }
  return ret;
}

bool pdg::Node::isAddrVarNode()
{
  for (auto in_edge : _in_edge_set)
  {
    if (in_edge.getEdgeType() == EdgeType::PARAMETER_IN && in_edge.getSrcNode()->getNodeType() == GraphNodeType::FORMAL_IN)
      return true;
  }
  return false;
}

pdg::Node *pdg::Node::getAbstractTreeNode()
{
  for (auto in_edge : _in_edge_set)
  {
    if (in_edge.getEdgeType() == EdgeType::PARAMETER_IN && in_edge.getSrcNode()->getNodeType() == GraphNodeType::FORMAL_IN)
      return in_edge.getSrcNode();
  }
  return nullptr;
}
