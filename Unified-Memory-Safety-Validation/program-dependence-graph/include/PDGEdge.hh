#ifndef PDGEDGE_H_
#define PDGEDGE_H_
#include "PDGNode.hh"
#include "PDGEnums.hh"

namespace pdg
{
  class Node;
  class Edge
  {
  private:
    EdgeType _edge_type;
    Node *_source;
    Node *_dst;

  public:
    Edge() = delete;
    Edge(Node *source, Node *dst, EdgeType edge_type)
    {
      _source = source;
      _dst = dst;
      _edge_type = edge_type;
    }
    Edge(const Edge &e) // copy constructor
    {
      _source = e.getSrcNode();
      _dst = e.getDstNode();
      _edge_type = e.getEdgeType();
    }

    EdgeType getEdgeType() const { return _edge_type; }
    Node *getSrcNode() const { return _source; }
    Node *getDstNode() const { return _dst; }
    bool operator<(const Edge &e) const
    {
      return (_source == e.getSrcNode() && _dst == e.getDstNode() && _edge_type == e.getEdgeType());
    }

    bool operator==(const Edge& otherEdge) const
    {
      if (this->getSrcNode() == otherEdge.getSrcNode() && this->getDstNode() == otherEdge.getDstNode() && this->getEdgeType() == otherEdge.getEdgeType())
        return true;
      else
        return false;
    }

    struct HashFunction
    {
      size_t operator()(const Edge& edge) const
      {
        size_t srcHash = std::hash<int>()(reinterpret_cast<std::intptr_t>(edge.getSrcNode()));
        size_t dstHash = std::hash<int>()(reinterpret_cast<std::intptr_t>(edge.getDstNode()));
        size_t edgeTypeHash = std::hash<int>()(static_cast<int>(edge.getEdgeType()));
        return srcHash ^ (dstHash << 1) ^ (edgeTypeHash << 2);
      }
    };
  };

} // namespace Edge

#endif