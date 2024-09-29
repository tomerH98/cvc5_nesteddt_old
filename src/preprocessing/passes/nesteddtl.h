#ifndef CVC5__PREPROCESSING__PASSES__NESTEDDTL_H
#define CVC5__PREPROCESSING__PASSES__NESTEDDTL_H

#include "cvc5_private.h"
#include "preprocessing/preprocessing_pass.h"
#include "expr/node.h"
#include "expr/dtype.h"
#include <set>
#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
#include <boost/graph/strong_components.hpp>


typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS> Graph;
typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::undirectedS> UndirectedGraph;
typedef boost::graph_traits<Graph>::vertex_descriptor Vertex;
typedef std::pair<int, int> Edge;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Class implementing a simplified version of Nesteddtl preprocessing pass.
 */
class Nesteddtl : public PreprocessingPass
{
 public:
  /**
   * Constructor for Nesteddtl pass.
   *
   * @param preprocContext The preprocessing context
   */
  Nesteddtl(PreprocessingPassContext* preprocContext);
  static inline const std::string nested_prefix = "nested_datatype_prefix";

 protected:
  /**
   * Apply a simplified preprocessing pass that replaces every assertion with 'false'.
   *
   * @param assertionsToPreprocess The pipeline of assertions to preprocess
   * @return The result of the preprocessing pass application
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
   // let's define a constant string for the new datatype name
  /**
   * Analyze the assertions and find the set of constructored types, array types, variables and select assertions.
   *
   * @param assertionsToPreprocess The pipeline of assertions to preprocess
   * @param constructoredTypes The set of constructored types
   * @param arrayTypes The set of array types
   * @param vars The set of variables
   * @param selectAssertions The map of TypeNode to Node representing the select assertions
   * @param arrays The set of arrays
   * @param storeNodes The set of store nodes
   * @param selectNodes The set of select nodes
   * @param functionNodes The set of function nodes
   */
  void analyzeAssertions(AssertionPipeline* assertionsToPreprocess, std::set<TypeNode>* constructoredTypes, std::set<TypeNode>* arrayTypes, std::set<Node>* vars, std::set<Node>* boundVars, std::map<TypeNode, std::vector<Node>>* selectAssertions, std::set<Node>* arrays, std::set<Node>* storeNodes, std::set<Node>* selectNodes, std::set<Node>* functionNodes, std::set<TypeNode>* seqTypes, std::map<TypeNode, std::vector<Node>>* seqNthAssertions, std::set<Node>* seqs, std::set<Node>* seqNthNodes, std::set<TypeNode>* typesSet, std::map<TypeNode, int>* typeNodeMap, std::map<int, TypeNode>* typeNodeMapRev, std::map<TypeNode, std::set<int>>* typeNodeIntSet);

  void filterDT(std::set<TypeNode>* constructoredTypes, std::set<TypeNode>* arrayTypes, std::set<Node>* vars, std::map<TypeNode, std::vector<Node>>* selectAssertions, std::set<Node>* arrays, std::set<Node>* storeNodes, std::set<Node>* selectNodes, std::set<Node>* functionNodes, std::set<TypeNode>* seqTypes, std::map<TypeNode, std::vector<Node>>* seqNthAssertions, std::set<Node>* seqs, std::set<int>* cycleNodes, std::map<TypeNode, int>* typeNodeMap);

  void createGraph(Graph* g, std::set<TypeNode>* typesSet, std::map<TypeNode, int>* typeNodeMap, std::map<int, TypeNode>* typeNodeMapRev);

  void nodeCycleDetector(Graph* g, std::set<int>* cycleTypes, std::map<int, TypeNode>* typeNodeMapRev);

  /**
   * Creates a map of DType for the recursive DT.
   *
   * @param constructoredTypes The set of constructored types
   * @param arrayTypes The set of array types
   * @param map The map of TypeNode to DType
   */
  void declareNewTypes(std::set<TypeNode>* constructoredTypes, std::set<TypeNode>* arrayTypes, std::set<TypeNode>* seqTypes, std::map<TypeNode, DType>* mapDType, std::map<TypeNode, TypeNode>* mapTypeNode, NodeManager* nm);


  /**
   * Add the new arrrays to the map
   *
   * @param map The map to change
   * @param arrayTypes The set of array types
   * @param selectAssertions The set of select assertions
   * @param nm The node manager
   */
  void defineArraySeqInMap(std::map<TypeNode, DType>* mapDType, std::map<TypeNode, TypeNode>* mapTypeNode, std::set<TypeNode>* arrayTypes, std::set<TypeNode>* seqTypes, std::map<TypeNode, std::vector<Node>>* selectAssertions, std::map<TypeNode, std::vector<Node>>* seqNthAssertions, NodeManager* nm);

  /**
   * Construct all the constructored types in the map
   *
   * @param map The map to change
   * @param nm The node manager
   */
  void defineConstructoredInMap(std::map<TypeNode, DType>* map, std::map<TypeNode, TypeNode>* mapTypeNode, NodeManager* nm);

  /**
   * Create a map of TypeNode to TypeNode from the old map
   *
   * @param map The old map that needs to be resolved
   * @param nm The node manager
   * @param resolvedMap The new map
   */
  void createResolvedMap(std::map<TypeNode, DType>* map, NodeManager* nm, std::map<TypeNode, TypeNode>* resolvedMap);

  /*
    * Convert a given type to a new type.
    *
    * @param type The type to convert
    * @param newTypes The map of the old types to the new types
    * @param nm The node manager
    * @return A TypeNode object representing the new type
  */
  TypeNode convertTypeNode(TypeNode type, std::map<TypeNode, TypeNode>* resolvedMap);

  /**
   * Create a map of TypeNode to TypeNode from the old vars to the new vars
   *
   * @param map The map of the old types to the new types
   * @param vars The vars to change
   * @param nm The node manager
   * @param varsMap The new map
   */
  void createVarsFuncsMap(std::map<TypeNode, TypeNode>* map, std::set<Node>* vars, NodeManager* nm, std::map<Node, Node>* varsMap, std::set<Node>* functionNodes);

  /**
   * Create a map from array types to their UF
   * @param map The map of the old arrays to the new recursive arrays
   * @param nm The node manager
   * @param ufArrays The new map
   */
  void createUFArrays(std::map<TypeNode, TypeNode>* map, NodeManager* nm, std::map<TypeNode, std::vector<Node>>* ufArrays);

  /**
   * Translate a single assertion to the new recursive types
   * @param node The assertion to translate
   * @param varsMap The map of the old vars to the new vars
   * @param ufArrays The map of the old arrays to the new recursive arrays
   * @param resolvedMap The map of the old types to the new types
   * @return The new assertions
   */
  Node translateNode(const Node node, std::map<Node, Node> varsMap, std::map<TypeNode, std::vector<Node>> ufArrays, std::map<TypeNode, TypeNode> resolvedMap, NodeManager* nm, std::map<Node, Node>* nodeMap);

  void translateVar(Node current, std::map<Node, Node>* nodeMap, std::map<Node, Node>* varsMap);

  void translateOperator(Node current, NodeManager* nm, std::map<Node, Node>* nodeMap,  std::map<Node, Node>* varsMap);

  void addAssertionsArrays(std::set<Node>* selectNodes, std::set<Node>* boundVars, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::set<Node>* arrays, std::map<Node, Node>* nodeMap);

  void addAssertionsSeqs(std::set<Node>* seqNthNodes, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::set<Node>* seqs, std::map<Node, Node>* nodeMap);

  void populateSingleton(std::map<TypeNode, TypeNode>* resolvedMap, std::set<Node>* arrays, std::map<Node, Node>* nodeMap, std::map<TypeNode, std::vector<Node>>* ufArrays);

};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__NESTEDDTL_H */
