#include "preprocessing/passes/nesteddt.h"

#include <set>
#include <stack>
#include <typeinfo>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"

using namespace cvc5::internal;
using namespace boost;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Nesteddt::Nesteddt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "nesteddt")
{
}

PreprocessingPassResult Nesteddt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // Get the NodeManager
  NodeManager* nm = NodeManager::currentNM();

  // print assertions
  for (size_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    Node assertion = (*assertionsToPreprocess)[i];
    Trace("nesteddttag") << "Assertion " << i << ": " << assertion.toString()
                         << " kind: " << assertion.getKind() << std::endl;
  }

  std::set<TypeNode> constructoredTypes;
  std::set<TypeNode> arrayTypes;
  std::set<Node> vars;
  std::map<TypeNode, std::vector<Node>> selextIndexes;
  std::set<Node> arrays;
  std::set<Node> storeNodes;
  std::set<Node> selectNodes;
  std::set<Node> functionNodes;
  std::set<TypeNode> seqTypes;
  std::map<TypeNode, std::vector<Node>> seqNthIndexes;
  std::set<Node> seqs;
  std::set<Node> seqNthNodes;
  std::map<int, TypeNode> typeNodeMapRev;
  std::map<TypeNode, int> typeNodeMap;
  std::map<const TNode, std::set<int>> dependentTypes;
  analyzeAssertions(assertionsToPreprocess,
                    &constructoredTypes,
                    &arrayTypes,
                    &vars,
                    &selextIndexes,
                    &arrays,
                    &storeNodes,
                    &selectNodes,
                    &functionNodes,
                    &seqTypes,
                    &seqNthIndexes,
                    &seqs,
                    &seqNthNodes,
                    &typeNodeMap,
                    &typeNodeMapRev,
                    &dependentTypes);

  Graph g;
  createGraph(&g, &typeNodeMap, &typeNodeMapRev);

  std::set<int> cycleNodes;
  nodeCycleDetector(&g, &cycleNodes, &typeNodeMapRev);

  // print the cycleNodes
  for (const auto& cycleNode : cycleNodes)
  {
    Assert(typeNodeMapRev.find(cycleNode) != typeNodeMapRev.end());
    Trace("nesteddttag") << "Cycle node type: " << typeNodeMapRev[cycleNode]
                         << std::endl;
  }

  filterDT(&constructoredTypes,
           &arrayTypes,
           &vars,
           &selextIndexes,
           &arrays,
           &storeNodes,
           &selectNodes,
           &functionNodes,
           &seqTypes,
           &seqNthIndexes,
           &seqs,
           &cycleNodes,
           &typeNodeMap);

  // Create a map between the constructored types and arrays and the new types
  std::map<TypeNode, DType> mapDType;
  std::map<TypeNode, TypeNode> mapTypeNode;
  declareNewTypes(
      &constructoredTypes, &arrayTypes, &seqTypes, &mapDType, &mapTypeNode, nm);

  // Define the array types in the map
  defineArraySeqInMap(&mapDType,
                      &mapTypeNode,
                      &arrayTypes,
                      &seqTypes,
                      &selextIndexes,
                      &seqNthIndexes,
                      nm);

  // Define the constructored types in the map
  defineConstructoredInMap(&mapDType, &mapTypeNode, nm);

  // Resolve the map
  std::map<TypeNode, TypeNode> resolvedMap;
  createResolvedMap(&mapDType, nm, &resolvedMap);
  // print the resolvedMap
  for (const auto& pair : resolvedMap)
  {
    Trace("nesteddttag") << "createResolvedMap - Old type: " << pair.first
                         << " New type: " << pair.second << std::endl;
    Trace("nesteddttag") << "createResolvedMap - New Dtype: "
                         << pair.second.getDType() << std::endl;
  }

  // Create a map between the vars and the new vars
  std::map<Node, Node> varsMap;
  createVarsFuncsMap(&resolvedMap, &vars, nm, &varsMap, &functionNodes);
  // iterate over vars
  for (const auto& var : vars)
  {
    Assert(varsMap.find(var) != varsMap.end());
    Trace("nesteddttag") << "createVarsMap - Old var: " << var
                         << " New var: " << varsMap[var] << std::endl;
    Trace("nesteddttag") << "createVarsMap - Old var type: " << var.getType()
                         << " New var type: " << varsMap[var].getType()
                         << std::endl;
  }

  // Create a map between the array types and the uninterpreted functions
  std::map<TypeNode, std::vector<Node>> ufArrays;
  createUFArrays(&resolvedMap, nm, &ufArrays);

  Trace("nesteddttag") << "after createUFArrays" << std::endl;

  std::map<Node, Node> nodeMap;

  for (size_t index = 0, n = assertionsToPreprocess->size(); index < n; ++index)
  {
    // Get a reference to the assertion stored in the vector.
    const Node& assertion = (*assertionsToPreprocess)[index];
    Assert(dependentTypes.find(assertion) != dependentTypes.end());

    // Compute the intersection between dependent types for this assertion and
    // the cycleNodes.
    std::set<int> intersection;
    std::set_intersection(dependentTypes.at(assertion).begin(),
                          dependentTypes.at(assertion).end(),
                          cycleNodes.begin(),
                          cycleNodes.end(),
                          std::inserter(intersection, intersection.begin()));

    // If there is no intersection, skip this assertion.
    if (!intersection.empty())
    {
      // Translate the assertion and update it in the pipeline.
      Node newAssertion = translateNode(
          assertion, varsMap, ufArrays, resolvedMap, nm, &nodeMap);
      assertionsToPreprocess->replace(index, newAssertion);
      // print the new assertion
      Trace("nesteddttag") << "New assertion: " << newAssertion.toString()
                           << std::endl;
    }
  }

  Trace("nesteddttag") << "___________________________" << std::endl;
  // print assertions
  for (size_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    Trace("nesteddttag") << "(assert "
                         << (*assertionsToPreprocess)[i].toString() << ")"
                         << std::endl;
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

void Nesteddt::createGraph(Graph* g,
                           std::map<TypeNode, int>* typeNodeMap,
                           std::map<int, TypeNode>* typeNodeMapRev)
{
  std::vector<Edge> edges;

  for (const auto& [type, typeIdx] : *typeNodeMap)
  {
    Trace("nesteddttag") << "Processing type: " << type
                         << " with index: " << typeIdx << std::endl;

    if (type.isDatatype())
    {
      const DType& dtype = type.getDType();
      size_t numConstructors = dtype.getNumConstructors();
      Trace("nesteddttag") << "  Datatype with " << numConstructors
                           << " constructors" << std::endl;

      for (size_t i = 0; i < numConstructors; ++i)
      {
        const DTypeConstructor& constructor = dtype[i];
        Trace("nesteddttag")
            << "    Constructor " << i << ": " << constructor.getName()
            << " with " << constructor.getNumArgs() << " arguments"
            << std::endl;

        for (size_t j = 0, n = constructor.getNumArgs(); j < n; ++j)
        {
          TypeNode argType = constructor[j].getRangeType();
          Trace("nesteddttag")
              << "      Arg " << j << " has type: " << argType << std::endl;

          if (typeNodeMap->find(type) != typeNodeMap->end()
              && typeNodeMap->find(argType) != typeNodeMap->end())
          {
            int from = (*typeNodeMap)[type];
            int to = (*typeNodeMap)[argType];
            edges.emplace_back(from, to);
            Trace("nesteddttag") << "        Adding edge from " << from
                                 << " to " << to << std::endl;
          }
        }
      }
    }
    else if (type.isArray())
    {
      TypeNode elementType = type.getArrayConstituentType();
      Trace("nesteddttag") << "  Array type, element type: " << elementType
                           << std::endl;

      if (typeNodeMap->find(type) != typeNodeMap->end()
          && typeNodeMap->find(elementType) != typeNodeMap->end())
      {
        int from = (*typeNodeMap)[type];
        int to = (*typeNodeMap)[elementType];
        edges.emplace_back(from, to);
        Trace("nesteddttag")
            << "    Adding edge from " << from << " to " << to << std::endl;
      }
    }
    else if (type.isSequence())
    {
      TypeNode elementType = type.getSequenceElementType();
      Trace("nesteddttag") << "  Sequence type, element type: " << elementType
                           << std::endl;

      if (typeNodeMap->find(type) != typeNodeMap->end()
          && typeNodeMap->find(elementType) != typeNodeMap->end())
      {
        int from = (*typeNodeMap)[type];
        int to = (*typeNodeMap)[elementType];
        edges.emplace_back(from, to);
        Trace("nesteddttag")
            << "    Adding edge from " << from << " to " << to << std::endl;
      }
    }
  }

  // Add edges to the graph
  for (const auto& edge : edges)
  {
    add_edge(edge.first, edge.second, *g);
  }
}

void Nesteddt::nodeCycleDetector(Graph* g,
                                 std::set<int>* cycleTypes,
                                 std::map<int, TypeNode>* typeNodeMapRev)
{
  // Create the reverse graph
  Graph reverse_g(num_vertices(*g));
  graph_traits<Graph>::edge_iterator ei, ei_end;
  for (boost::tie(ei, ei_end) = edges(*g); ei != ei_end; ++ei)
  {
    add_edge(target(*ei, *g), source(*ei, *g), reverse_g);
  }

  // Compute the Strong Components (SCCs)
  std::vector<int> component(num_vertices(*g)), discover_time(num_vertices(*g));
  std::vector<default_color_type> color(num_vertices(*g));
  std::vector<Vertex> root(num_vertices(*g));
  int num = strong_components(
      *g,
      make_iterator_property_map(component.begin(), get(vertex_index, *g)),
      root_map(make_iterator_property_map(root.begin(), get(vertex_index, *g)))
          .color_map(
              make_iterator_property_map(color.begin(), get(vertex_index, *g)))
          .discover_time_map(make_iterator_property_map(
              discover_time.begin(), get(vertex_index, *g))));

  std::vector<int> component_sizes(num, 0);
  for (int comp_id : component)
  {
    ++component_sizes[comp_id];
  }

  // Process each SCC
  std::vector<bool> visited(num_vertices(*g), false);
  for (size_t i = 0; i < component.size(); ++i)
  {
    if (component_sizes[component[i]] > 1)
    {
      bool hasArrayType = false;
      int startNode = -1;
      for (size_t j = 0; j < component.size(); ++j)
      {
        if (component[j] == component[i]
            && (typeNodeMapRev->at(j).isArray()
                || typeNodeMapRev->at(j).isSequence()))
        {
          hasArrayType = true;
          startNode = j;
          break;
        }
      }
      if (hasArrayType)
      {
        // Perform DFS from startNode
        std::stack<int> stack;
        stack.push(startNode);

        while (!stack.empty())
        {
          int node = stack.top();
          stack.pop();

          if (!visited[node])
          {
            visited[node] = true;
            cycleTypes->insert(node);

            // add the children of the current node to the stack
            graph_traits<Graph>::adjacency_iterator ai, ai_end;
            for (boost::tie(ai, ai_end) = adjacent_vertices(node, reverse_g);
                 ai != ai_end;
                 ++ai)
            {
              stack.push(*ai);
            }
          }
        }
      }
    }
  }
}

void Nesteddt::analyzeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    std::set<TypeNode>* constructoredTypes,
    std::set<TypeNode>* arrayTypes,
    std::set<Node>* vars,
    std::map<TypeNode, std::vector<Node>>* selectAssertions,
    std::set<Node>* arrays,
    std::set<Node>* storeNodes,
    std::set<Node>* selectNodes,
    std::set<Node>* functionNodes,
    std::set<TypeNode>* seqTypes,
    std::map<TypeNode, std::vector<Node>>* seqNthAssertions,
    std::set<Node>* seqs,
    std::set<Node>* seqNthNodes,
    std::map<TypeNode, int>* typeNodeMap,
    std::map<int, TypeNode>* typeNodeMapRev,
    std::map<const TNode, std::set<int>>* dependentTypes)
{
  std::set<Node> visitedNodes;
  std::map<TypeNode, std::set<Node>> selectAssertionsSet;
  std::map<TypeNode, std::set<Node>> seqNthAssertionsSet;
  size_t assertions_size = assertionsToPreprocess->size();

  for (size_t idx = 0; idx < assertions_size; ++idx)
  {
    Trace("nesteddttag") << "Analyzing assertion " << idx << ": "
                         << (*assertionsToPreprocess)[idx] << std::endl;
    // Traverse the assertion's AST.
    for (TNode current : NodeDfsIterable((*assertionsToPreprocess)[idx]))
    {
      // Skip if already processed.
      if (!visitedNodes.insert(current).second)
      {
        continue;
      }
      // Process the node.
      processNode(current,
                  constructoredTypes,
                  arrayTypes,
                  vars,
                  arrays,
                  seqTypes,
                  seqs,
                  selectNodes,
                  seqNthNodes,
                  storeNodes,
                  functionNodes,
                  typeNodeMap,
                  typeNodeMapRev,
                  dependentTypes);
    }
  }

  // Build maps of index assertions from SELECT and SEQ_NTH nodes.
  collectArrInd(*storeNodes, *selectNodes, selectAssertionsSet);
  collectSeqInd(*seqNthNodes, seqNthAssertionsSet);

  // Debug print of select assertions.
  for (const auto& pair : selectAssertionsSet)
  {
    Trace("nesteddttag") << "Select assertions for type: " << pair.first
                         << std::endl;
    for (const Node& idx : pair.second)
    {
      Trace("nesteddttag") << "  Index: " << idx << std::endl;
    }
  }

  // Convert sets to vectors for the output maps.
  convertAssertionsMap(selectAssertionsSet, *selectAssertions);
  convertAssertionsMap(seqNthAssertionsSet, *seqNthAssertions);
}

// Processes a single AST node and updates the analysis data structures.
void Nesteddt::processNode(const TNode& current,
                           std::set<TypeNode>* constructoredTypes,
                           std::set<TypeNode>* arrayTypes,
                           std::set<Node>* vars,
                           std::set<Node>* arrays,
                           std::set<TypeNode>* seqTypes,
                           std::set<Node>* seqs,
                           std::set<Node>* selectNodes,
                           std::set<Node>* seqNthNodes,
                           std::set<Node>* storeNodes,
                           std::set<Node>* functionNodes,
                           std::map<TypeNode, int>* typeNodeMap,
                           std::map<int, TypeNode>* typeNodeMapRev,
                           std::map<const TNode, std::set<int>>* dependentTypes)
{
  Trace("nesteddttag") << "Visiting node: " << current
                       << " of kind: " << current.getKind()
                       << " and type: " << current.getType() << std::endl;
  TypeNode type = current.getType();
  // If the type is new, update type maps.
  if (typeNodeMap->find(type) == typeNodeMap->end())
  {
    int index = typeNodeMap->size();
    typeNodeMap->insert({type, index});
    typeNodeMapRev->insert({typeNodeMapRev->size(), type});
    Trace("nesteddttag") << "New type encountered: " << type
                         << " assigned index: " << index << std::endl;
  }
  // Record variable nodes.
  if (current.isVar())
  {
    vars->insert(current);
    Trace("nesteddttag") << "Variable added: " << current << std::endl;
  }
  // Categorize the node by its type.
  if (type.isDatatype())
  {
    constructoredTypes->insert(type);
    Trace("nesteddttag") << "Datatype type detected: " << type << std::endl;
  }
  if (type.isArray())
  {
    arrayTypes->insert(type);
    arrays->insert(current);
    Trace("nesteddttag") << "Array type detected: " << type
                         << ", node: " << current << std::endl;
  }
  if (type.isSequence())
  {
    seqTypes->insert(type);
    seqs->insert(current);
    Trace("nesteddttag") << "Sequence type detected: " << type
                         << ", node: " << current << std::endl;
  }
  // Categorize nodes by their kind.
  if (current.getKind() == Kind::SELECT)
  {
    selectNodes->insert(current);
    Trace("nesteddttag") << "SELECT node found: " << current << std::endl;
  }
  if (current.getKind() == Kind::SEQ_NTH)
  {
    seqNthNodes->insert(current);
    Trace("nesteddttag") << "SEQ_NTH node found: " << current << std::endl;
  }
  if (current.getKind() == Kind::STORE)
  {
    storeNodes->insert(current);
    Trace("nesteddttag") << "STORE node found: " << current << std::endl;
  }
  if (current.getKind() == Kind::APPLY_UF)
  {
    if (current.getOperator().getType().isFunction())
    {
      functionNodes->insert(current.getOperator());
      Trace("nesteddttag") << "Function application found: "
                           << current.getOperator() << std::endl;
    }
  }
  // Initialize dependent types for this node.
  (*dependentTypes)[current] = std::set<int>();
  int currentIdx = (*typeNodeMap)[type];
  (*dependentTypes)[current].insert(currentIdx);

  // Merge dependent types from child nodes.
  for (const TNode& childNode : current)
  {
    Assert(dependentTypes->find(childNode) != dependentTypes->end());
    (*dependentTypes)[current].insert((*dependentTypes)[childNode].begin(),
                                      (*dependentTypes)[childNode].end());
  }

  Trace("nesteddttag") << "Dependent types for " << current << ": ";
  for (int dep : (*dependentTypes)[current])
  {
    Trace("nesteddttag") << dep << " ";
  }
  Trace("nesteddttag") << std::endl;
}

// Populates a map from TypeNode to a set of index nodes from SELECT nodes.
void Nesteddt::collectArrInd(
    const std::set<Node>& storeNodes,
    const std::set<Node>& selectNodes,
    std::map<TypeNode, std::set<Node>>& selectAssertionsSet)
{
  for (const Node& selectNode : selectNodes)
  {
    Node array = selectNode[0];
    Node index = selectNode[1];
    TypeNode arrayType = array.getType();
    selectAssertionsSet[arrayType].insert(index);
  }

  for (const Node& selectNode : storeNodes)
  {
    Node array = selectNode[0];
    Node index = selectNode[1];
    TypeNode arrayType = array.getType();
    selectAssertionsSet[arrayType].insert(index);
  }
}

// Populates a map from TypeNode to a set of index nodes from SEQ_NTH nodes.
void Nesteddt::collectSeqInd(
    const std::set<Node>& seqNthNodes,
    std::map<TypeNode, std::set<Node>>& seqNthAssertionsSet)
{
  for (const Node& seqNthNode : seqNthNodes)
  {
    Node seq = seqNthNode[0];
    Node index = seqNthNode[1];
    TypeNode seqType = seq.getType();
    seqNthAssertionsSet[seqType].insert(index);
  }
}

// Converts a map from TypeNode -> set<Node> to TypeNode -> vector<Node>.
void Nesteddt::convertAssertionsMap(
    const std::map<TypeNode, std::set<Node>>& inMap,
    std::map<TypeNode, std::vector<Node>>& outMap)
{
  for (const auto& pair : inMap)
  {
    outMap[pair.first] =
        std::vector<Node>(pair.second.begin(), pair.second.end());
  }
}

bool Nesteddt::isTypeExcluded(const TypeNode& type,
                              const std::set<int>* cycleNodes,
                              const std::map<TypeNode, int>* typeNodeMap)
{
  Assert(typeNodeMap->find(type) != typeNodeMap->end());
  // Return true if the type's index is NOT in the cycle set.
  return cycleNodes->find(typeNodeMap->at(type)) == cycleNodes->end();
}

// External helper: eraseIf
template <typename Container, typename Predicate>
void eraseIf(Container* container, Predicate pred)
{
  for (auto it = container->begin(); it != container->end();)
  {
    if (pred(*it))
    {
      it = container->erase(it);
    }
    else
    {
      ++it;
    }
  }
}

void Nesteddt::filterDT(std::set<TypeNode>* constructoredTypes,
                        std::set<TypeNode>* arrayTypes,
                        std::set<Node>* vars,
                        std::map<TypeNode, std::vector<Node>>* selectAssertions,
                        std::set<Node>* arrays,
                        std::set<Node>* storeNodes,
                        std::set<Node>* selectNodes,
                        std::set<Node>* functionNodes,
                        std::set<TypeNode>* seqTypes,
                        std::map<TypeNode, std::vector<Node>>* seqNthAssertions,
                        std::set<Node>* seqs,
                        std::set<int>* cycleNodes,
                        std::map<TypeNode, int>* typeNodeMap)
{
  // For containers holding TypeNode directly.
  eraseIf(constructoredTypes,
          [this, cycleNodes, typeNodeMap](const TypeNode& t) {
            return isTypeExcluded(t, cycleNodes, typeNodeMap);
          });
  eraseIf(arrayTypes, [this, cycleNodes, typeNodeMap](const TypeNode& t) {
    return isTypeExcluded(t, cycleNodes, typeNodeMap);
  });
  eraseIf(seqTypes, [this, cycleNodes, typeNodeMap](const TypeNode& t) {
    return isTypeExcluded(t, cycleNodes, typeNodeMap);
  });

  // For containers holding Node, check the node's type.
  eraseIf(vars, [this, cycleNodes, typeNodeMap](const Node& var) {
    return isTypeExcluded(var.getType(), cycleNodes, typeNodeMap);
  });
  eraseIf(arrays, [this, cycleNodes, typeNodeMap](const Node& array) {
    return isTypeExcluded(array.getType(), cycleNodes, typeNodeMap);
  });
  eraseIf(seqs, [this, cycleNodes, typeNodeMap](const Node& seq) {
    return isTypeExcluded(seq.getType(), cycleNodes, typeNodeMap);
  });

  // For storeNodes and selectNodes, check the type of the first child.
  eraseIf(storeNodes, [this, cycleNodes, typeNodeMap](const Node& storeNode) {
    return isTypeExcluded(storeNode[0].getType(), cycleNodes, typeNodeMap);
  });
  eraseIf(selectNodes, [this, cycleNodes, typeNodeMap](const Node& selectNode) {
    return isTypeExcluded(selectNode[0].getType(), cycleNodes, typeNodeMap);
  });

  // Special handling for functionNodes.
  // Remove a function node only if its output type is excluded
  // and every input type is also excluded.
  eraseIf(
      functionNodes,
      [this, cycleNodes, typeNodeMap](const Node& functionNode) -> bool {
        TypeNode outputType = functionNode.getType().getRangeType();
        const auto& inputTypes = functionNode.getType().getArgTypes();
        return isTypeExcluded(outputType, cycleNodes, typeNodeMap)
               && std::all_of(
                   inputTypes.begin(),
                   inputTypes.end(),
                   [this, cycleNodes, typeNodeMap](const TypeNode& inputType) {
                     return isTypeExcluded(inputType, cycleNodes, typeNodeMap);
                   });
      });
}

void Nesteddt::declareNewTypes(std::set<TypeNode>* constructoredTypes,
                               std::set<TypeNode>* arrayTypes,
                               std::set<TypeNode>* seqTypes,
                               std::map<TypeNode, DType>* mapDType,
                               std::map<TypeNode, TypeNode>* mapTypeNode,
                               NodeManager* nm)
{
  std::stringstream ss;
  TypeNode unresSort;
  // Iterate over constructoredTypes
  for (const auto& constructoredType : (*constructoredTypes))
  {
    ss.str("");
    ss << constructoredType << "_rc";
    // Declare a new type for each constructoredType
    DType newDType(ss.str());
    (*mapDType).insert(std::pair<TypeNode, DType>(constructoredType, newDType));

    unresSort = nm->mkUnresolvedDatatypeSort(ss.str());
    (*mapTypeNode)
        .insert(std::pair<TypeNode, TypeNode>(constructoredType, unresSort));
  }

  for (const auto& arrayType : (*arrayTypes))
  {
    ss.str("");
    ss << "Array_[" << arrayType.getArrayIndexType() << "_"
       << arrayType.getArrayConstituentType() << "]_rc";
    // Declare a new type for each arrayType
    DType newDType(ss.str());
    (*mapDType).insert(std::pair<TypeNode, DType>(arrayType, newDType));

    unresSort = nm->mkUnresolvedDatatypeSort(ss.str());
    (*mapTypeNode).insert(std::pair<TypeNode, TypeNode>(arrayType, unresSort));
  }

  for (const auto& seqType : (*seqTypes))
  {
    ss.str("");
    ss << "Seq_" << seqType.getSequenceElementType() << "_rc";
    // Declare a new type for each arrayType
    DType newDType(ss.str());
    (*mapDType).insert(std::pair<TypeNode, DType>(seqType, newDType));

    unresSort = nm->mkUnresolvedDatatypeSort(ss.str());
    (*mapTypeNode).insert(std::pair<TypeNode, TypeNode>(seqType, unresSort));
  }
}

void Nesteddt::defineArraySeqInMap(
    std::map<TypeNode, DType>* mapDType,
    std::map<TypeNode, TypeNode>* mapTypeNode,
    std::set<TypeNode>* arrayTypes,
    std::set<TypeNode>* seqTypes,
    std::map<TypeNode, std::vector<Node>>* selectAssertions,
    std::map<TypeNode, std::vector<Node>>* seqNthAssertions,
    NodeManager* nm)
{
  std::stringstream ss;
  // Iterate over arrayTypes
  for (const auto& arrayType : (*arrayTypes))
  {
    // Get the arrayType's DType from the mapDType
    auto it = (*mapDType).find(arrayType);
    Assert(it != (*mapDType).end());
    // The key exists in the mapDType, you can safely access it
    DType& newDType = it->second;
    // Get the DType of the arrayType
    TypeNode indexType = arrayType.getArrayIndexType();
    TypeNode elementType = arrayType.getArrayConstituentType();

    // Add a constructor for the array's elements
    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    // add the id as an argument to the constructor
    cons->addArg("id", nm->integerType());
    // Iterate over the select assertions of the arrayType
    newDType.addConstructor(cons);
    // Insert the new type into the mapDType
    (*mapDType).insert(std::pair<TypeNode, DType>(arrayType, newDType));
  }

  // Iterate over seqTypes
  for (const auto& seqType : (*seqTypes))
  {
    // Get the arrayType's DType from the mapDType
    auto it = (*mapDType).find(seqType);
    Assert(it != (*mapDType).end());
    // The key exists in the mapDType, you can safely access it
    DType& newDType = it->second;
    // Get the DType of the arrayType
    TypeNode elementType = seqType.getSequenceElementType();
    TypeNode newElementType = convertTypeNode(elementType, mapTypeNode);
    // Add a constructor for the array's elements
    std::shared_ptr<DTypeConstructor> cons =
        std::make_shared<DTypeConstructor>("cons");
    // add the id as an argument to the constructor
    cons->addArg("id", nm->integerType());
    newDType.addConstructor(cons);
    // Insert the new type into the mapDType
    (*mapDType).insert(std::pair<TypeNode, DType>(seqType, newDType));
  }
}

void Nesteddt::defineConstructoredInMap(
    std::map<TypeNode, DType>* mapDType,
    std::map<TypeNode, TypeNode>* mapTypeNode,
    NodeManager* nm)
{
  std::stringstream ss;
  // Iterate over mapDType
  for (const auto& pair : (*mapDType))
  {
    // Get the typeNode
    const TypeNode& typeNode = pair.first;
    // Check if typeNode is in an array type
    if (typeNode.isArray() || typeNode.isSequence())
    {
      continue;
    }
    Assert(typeNode.isDatatype());
    // Get the DType
    auto it = (*mapDType).find(typeNode);
    Assert(it != (*mapDType).end());
    // The key exists in the mapDType, you can safely access it
    DType& dtype = it->second;
    // Get the DType of the typeNode
    const DType& oldDtype = typeNode.getDType();
    // Get the number of constructors
    size_t numConstructors = oldDtype.getNumConstructors();
    // Iterate over the constructors
    for (size_t i = 0; i < numConstructors; ++i)
    {
      // Get the constructor
      const DTypeConstructor& constructor = oldDtype[i];
      // Get the name of the constructor
      ss.str("");
      ss << constructor.getName() << "_rc";
      // Create a new constructor
      std::shared_ptr<DTypeConstructor> newConstructor =
          std::make_shared<DTypeConstructor>(ss.str());
      // Get the number of arguments
      size_t numArgs = constructor.getNumArgs();
      // Iterate over the arguments
      for (size_t j = 0; j < numArgs; ++j)
      {
        // Get the selector
        const DTypeSelector& selector = constructor[j];
        // Get the name of the selector
        ss.str("");
        ss << selector.getName() << "_rc";
        // Get the type of the selector
        TypeNode selectorType = selector.getRangeType();
        // Convert the type of the selector
        TypeNode newSelectorType = convertTypeNode(selectorType, mapTypeNode);
        // Add the selector to the new constructor
        newConstructor->addArg(ss.str(), newSelectorType);
      }
      // Add the new constructor to the new DType
      dtype.addConstructor(newConstructor);
    }
  }
}

void Nesteddt::createResolvedMap(std::map<TypeNode, DType>* mapDType,
                                 NodeManager* nm,
                                 std::map<TypeNode, TypeNode>* resolvedMap)
{
  std::vector<DType> datatypes;
  std::vector<TypeNode> oldTypes;
  for (const auto& pair : (*mapDType))
  {
    oldTypes.push_back(pair.first);
    datatypes.push_back(pair.second);
  }
  // Using the mkMutualDatatypeTypes function to create the new types
  std::vector<TypeNode> resolvedTypes = nm->mkMutualDatatypeTypes(datatypes);

  // Create the map resolvedMap between the old types and the resolvedTypes
  for (size_t i = 0, n = oldTypes.size(); i < n; ++i)
  {
    (*resolvedMap)
        .insert(std::pair<TypeNode, TypeNode>(oldTypes[i], resolvedTypes[i]));
  }
}

TypeNode Nesteddt::convertTypeNode(TypeNode type,
                                   std::map<TypeNode, TypeNode>* typeMap)
{
  // check if the type is in the resolvedMap
  if (typeMap->find(type) != typeMap->end())
  {
    return (*typeMap)[type];
  }
  return type;
}

void Nesteddt::createVarsFuncsMap(std::map<TypeNode, TypeNode>* resolvedMap,
                                  std::set<Node>* vars,
                                  NodeManager* nm,
                                  std::map<Node, Node>* varsMap,
                                  std::set<Node>* functionNodes)
{
  // Iterate over vars
  Node newVar;
  TypeNode newType;
  std::stringstream newName;
  SkolemManager* sm = nm->getSkolemManager();

  for (const auto& var : (*vars))
  {
    newName.str("");
    newName << var.toString() << "_rc";
    newType = convertTypeNode(var.getType(), resolvedMap);
    newVar = sm->mkDummySkolem(newName.str(), newType);
    varsMap->insert(std::pair<Node, Node>(var, newVar));
    Trace("nesteddttag") << "Old var: " << var << " Old type: " << var.getType()
                         << " New var: " << newVar << " New type: " << newType
                         << std::endl;
  }

  // Iterate over functionNodes
  for (const auto& functionNode : (*functionNodes))
  {
    // get the functionNode name
    newName.str("");
    newName << functionNode.toString() << "_rc";
    TypeNode functionType = functionNode.getType();
    // get the functionNode input
    std::vector<TypeNode> functionInput = functionType.getArgTypes();
    // get the functionNode output
    TypeNode functionOutput = functionType.getRangeType();
    // convert the functionNode input
    std::vector<TypeNode> newFunctionInput;
    for (const auto& input : functionInput)
    {
      newType = convertTypeNode(input, resolvedMap);
      newFunctionInput.push_back(newType);
    }
    // convert the functionNode output
    TypeNode newFunctionOutput = convertTypeNode(functionOutput, resolvedMap);
    TypeNode newFunctionType =
        nm->mkFunctionType(newFunctionInput, newFunctionOutput);
    Node newFunctionNode = sm->mkDummySkolem(newName.str(), newFunctionType);
    varsMap->insert(std::pair<Node, Node>(functionNode, newFunctionNode));
    Trace("nesteddttag") << " New functionNode: " << newFunctionNode
                         << " New type: " << newFunctionType << std::endl;
  }

  // iterate over resolvedMap
  for (const auto& pair : (*resolvedMap))
  {
    // Get the typeNode
    const TypeNode& oldType = pair.first;
    const TypeNode& newResolvedType = pair.second;
    // Check if typeNode is in an array type
    if (oldType.isArray() || oldType.isSequence())
    {
      continue;
    }
    // Get the DType
    DType oldDType = oldType.getDType();
    DType newDType = newResolvedType.getDType();
    // Get the number of constructors
    size_t oldNumConstructors = oldDType.getNumConstructors();
    Assert(oldNumConstructors == newDType.getNumConstructors());
    // Iterate over the constructors
    for (size_t i = 0; i < oldNumConstructors; ++i)
    {
      // Get the constructor
      const DTypeConstructor& oldConstructor = oldDType[i];
      const DTypeConstructor& newConstructor = newDType[i];
      // Get the name of the constructor

      TNode oldConstructorNode = oldConstructor.getConstructor();
      TNode newConstructorNode = newConstructor.getConstructor();
      varsMap->insert(
          std::pair<Node, Node>(oldConstructorNode, newConstructorNode));
      // Get the number of arguments
      size_t oldNumArgs = oldConstructor.getNumArgs();
      Assert(oldNumArgs == newConstructor.getNumArgs());
      // Iterate over the arguments
      for (size_t j = 0; j < oldNumArgs; ++j)
      {
        varsMap->insert(std::pair<Node, Node>(oldConstructor.getSelector(j),
                                              newConstructor.getSelector(j)));
      }
    }
  }
}

void Nesteddt::createUFArrays(std::map<TypeNode, TypeNode>* map,
                              NodeManager* nm,
                              std::map<TypeNode, std::vector<Node>>* ufArrays)
{
  SkolemManager* sm = nm->getSkolemManager();
  // Iterate over map
  for (const auto& pair : (*map))
  {
    // Get the typeNode
    const TypeNode& oldArrayType = pair.first;
    // Check if typeNode is in an array type
    if (oldArrayType.isArray())
    {
      const TypeNode& consType = pair.second;
      TypeNode indexType = oldArrayType.getArrayIndexType();
      TypeNode elementType = oldArrayType.getArrayConstituentType();
      // create a new array type from the oldIndexType and oldElementType
      indexType = convertTypeNode(indexType, map);
      elementType = convertTypeNode(elementType, map);
      TypeNode newArrayType = nm->mkArrayType(indexType, elementType);

      // Create a old to new
      std::string consToArrName =
          "f_" + indexType.toString() + "_" + elementType.toString();
      Node consToArr = sm->mkDummySkolem(
          consToArrName, nm->mkFunctionType(consType, newArrayType));
      // Create a new to old
      std::string arrToOldName =
          "g_" + indexType.toString() + "_" + elementType.toString();
      Node arrToCons = sm->mkDummySkolem(
          arrToOldName, nm->mkFunctionType(newArrayType, consType));
      // Create a vector of the two uninterpreted functions
      std::vector<Node> ufArray;
      ufArray.push_back(consToArr);
      ufArray.push_back(arrToCons);

      // Insert the new type into the map
      ufArrays->insert(
          std::pair<TypeNode, std::vector<Node>>(oldArrayType, ufArray));
      ufArrays->insert(
          std::pair<TypeNode, std::vector<Node>>(newArrayType, ufArray));
      ufArrays->insert(
          std::pair<TypeNode, std::vector<Node>>(pair.second, ufArray));
    }
    else if (oldArrayType.isSequence())
    {
      const TypeNode& consType = pair.second;
      TypeNode elementType = oldArrayType.getSequenceElementType();
      // create a new array type from the oldIndexType and oldElementType
      elementType = convertTypeNode(elementType, map);
      TypeNode newSeqType = nm->mkSequenceType(elementType);

      // Create a old to new
      std::string consToArrName = consType.toString() + "_0";
      Node consToArr = sm->mkDummySkolem(
          consToArrName, nm->mkFunctionType(consType, newSeqType));
      // Create a new to old
      std::string arrToOldName = consType.toString() + "_1";
      Node arrToCons = sm->mkDummySkolem(
          arrToOldName, nm->mkFunctionType(newSeqType, consType));
      // Create a vector of the two uninterpreted functions
      std::vector<Node> ufArray;
      ufArray.push_back(consToArr);
      ufArray.push_back(arrToCons);

      // Insert the new type into the map
      ufArrays->insert(
          std::pair<TypeNode, std::vector<Node>>(oldArrayType, ufArray));
      ufArrays->insert(
          std::pair<TypeNode, std::vector<Node>>(newSeqType, ufArray));
      ufArrays->insert(
          std::pair<TypeNode, std::vector<Node>>(pair.second, ufArray));
    }
  }
  // print the ufArrays
  for (const auto& pair : (*ufArrays))
  {
    Trace("nesteddttag") << "createUFArrays: Old array type: " << pair.first
                         << std::endl;
    Trace("nesteddttag") << "createUFArrays: cons to arr: " << pair.second[0]
                         << " type: " << pair.second[0].getType() << std::endl;
    Trace("nesteddttag") << "createUFArrays: arr to cons: " << pair.second[1]
                         << " type: " << pair.second[1].getType() << std::endl;
  }
}

Node Nesteddt::consToArr(NodeManager* nm,
                         Node node,
                         std::map<TypeNode, std::vector<Node>>* ufArrays)
{
  Trace("nesteddttag") << "node: " << node << std::endl;
  TypeNode t = node.getType();
  Assert(t.isDatatype());
  Assert(ufArrays->find(t) != ufArrays->end());
  Node consToArr = (*ufArrays)[t][0];
  Node arrToCons = (*ufArrays)[t][1];
  if (node.getKind() == Kind::APPLY_UF && node.getOperator() == arrToCons)
  {
    return node[0];
  }
  Node consToArrApp = nm->mkNode(Kind::APPLY_UF, consToArr, node);
  return consToArrApp;
}

Node Nesteddt::arrToCons(NodeManager* nm,
                         Node node,
                         std::map<TypeNode, std::vector<Node>>* ufArrays)
{
  TypeNode t = node.getType();
  Assert(t.isArray() || t.isSequence());
  Assert(ufArrays->find(t) != ufArrays->end());
  Node consToArr = (*ufArrays)[t][0];
  Node arrToCons = (*ufArrays)[t][1];
  if (node.getKind() == Kind::APPLY_UF && node.getOperator() == consToArr)
  {
    return node[0];
  }
  Node arrToConsApp = nm->mkNode(Kind::APPLY_UF, arrToCons, node);
  return arrToConsApp;
}

Node Nesteddt::translateNode(const Node node,
                             std::map<Node, Node> varsMap,
                             std::map<TypeNode, std::vector<Node>> ufArrays,
                             std::map<TypeNode, TypeNode> resolvedMap,
                             NodeManager* nm,
                             std::map<Node, Node>* nodeMap)
{
  // check if node is in nodeMap, if so return its value
  if (nodeMap->find(node) != nodeMap->end())
  {
    return (*nodeMap)[node];
  }
  // Use node traversal to iterate the subnodes of node
  NodeDfsIterable nodeDfsIterable(node);
  for (TNode current : nodeDfsIterable)
  {
    // print the current node and its type
    Trace("nesteddttag") << "Current node: " << current
                         << ". Current node's type: " << current.getType()
                         << ". Current node's kind: " << current.getKind()
                         << std::endl;
    if (nodeMap->find(current) != nodeMap->end())
    {
      Trace("nesteddttag") << "already know: " << current << std::endl;
      continue;
    }
    if (current.hasOperator())
    {
      Trace("nesteddttag") << "Inside the hasOperator" << std::endl;
      translateOperator(current, nm, nodeMap, &varsMap, &ufArrays);
    }
    else
    {
      Trace("nesteddttag") << "Inside the isVar" << std::endl;
      translateVar(current, nodeMap, &varsMap);
    }

    // print the new node and its translation
    Trace("nesteddttag") << "Node: " << current
                         << " translation: " << (*nodeMap)[current]
                         << std::endl;
    Trace("nesteddttag") << "Node's type: " << current.getType()
                         << " translation's type: "
                         << (*nodeMap)[current].getType()
                         << " translation's kind: "
                         << (*nodeMap)[current].getKind() << std::endl;
  }

  return (*nodeMap)[node];
}

void Nesteddt::translateVar(Node current,
                            std::map<Node, Node>* nodeMap,
                            std::map<Node, Node>* varsMap)
{
  // check if the current node is in the varsMap
  if (varsMap->find(current) != varsMap->end())
  {
    Node n = (*varsMap)[current];
    nodeMap->insert(std::pair<Node, Node>(current, n));
  }
  else
  {
    nodeMap->insert(std::pair<Node, Node>(current, current));
  }
}

void Nesteddt::translateOperator(
    Node current,
    NodeManager* nm,
    std::map<Node, Node>* nodeMap,
    std::map<Node, Node>* varsMap,
    std::map<TypeNode, std::vector<Node>>* ufArrays)
{
  Node translatedChild;
  // get the operator
  Node operatorNode = current.getOperator();
  auto it = varsMap->find(operatorNode);
  if (it != varsMap->end())
  {
    operatorNode = it->second;
  }
  std::vector<TNode> newChildren;
  if (current.getKind() == Kind::BOUND_VAR_LIST)
  {
    for (size_t j = 0; j < current.getNumChildren(); ++j)
    {
      translatedChild = (*nodeMap)[current[j]];
      newChildren.push_back(translatedChild);
      Trace("nesteddttag") << "translatedChild: " << j << " " << translatedChild
                           << std::endl;
    }
  }
  else
  {
    for (size_t j = 0; j < current.getNumChildren(); ++j)
    {
      newChildren.push_back((*nodeMap)[current[j]]);
    }
  }
  std::set<Kind> kindSet = {
      Kind::APPLY_SELECTOR, Kind::APPLY_CONSTRUCTOR, Kind::APPLY_UF};
  if (kindSet.find(current.getKind()) != kindSet.end())
  {
    newChildren.insert(newChildren.begin(), operatorNode);
    Node newNode = nm->mkNode(current.getKind(), newChildren);
    nodeMap->insert(std::pair<Node, Node>(current, newNode));
  }
  else if (current.getKind() == Kind::SELECT
           || current.getKind() == Kind::SEQ_NTH)
  {
    Node newArray = (*nodeMap)[current[0]];
    Node newIndex = (*nodeMap)[current[1]];
    newArray = consToArr(nm, newArray, ufArrays);
    Node newSelect = nm->mkNode(current.getKind(), newArray, newIndex);
    nodeMap->insert(std::pair<Node, Node>(current, newSelect));
  }
  else if (current.getKind() == Kind::STORE)
  {
    Node newArray = (*nodeMap)[current[0]];
    Node newIndex = (*nodeMap)[current[1]];
    Node newValue = (*nodeMap)[current[2]];
    newArray = consToArr(nm, newArray, ufArrays);
    Node newStore = nm->mkNode(Kind::STORE, newArray, newIndex, newValue);
    newStore = arrToCons(nm, newStore, ufArrays);
    nodeMap->insert(std::pair<Node, Node>(current, newStore));
  }
  else
  {
    Node newNode = nm->mkNode(operatorNode, newChildren);
    nodeMap->insert(std::pair<Node, Node>(current, newNode));
  }
}
}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
