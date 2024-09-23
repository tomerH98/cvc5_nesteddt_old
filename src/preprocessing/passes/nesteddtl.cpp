#include "preprocessing/passes/nesteddtl.h"
#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_manager.h" 
#include "expr/skolem_manager.h"
#include "expr/node_traversal.h"
#include <typeinfo>
#include <stack>
#include <set>



using namespace cvc5::internal;
using namespace boost;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

Nesteddtl::Nesteddtl(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "nesteddtl") {
}

PreprocessingPassResult Nesteddtl::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
    // Get the NodeManager
    NodeManager* nm = NodeManager::currentNM();

    // print assertions
    for (size_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i) {
        Node assertion = (*assertionsToPreprocess)[i];
        Trace("nesteddtltag")  <<  "Assertion "  <<  i  <<  ": "  <<  assertion.toString()  <<  " kind: "  << assertion.getKind()  <<  std::endl;
    }

    std::set<TypeNode> constructoredTypes;
    std::set<TypeNode> arrayTypes;
    std::set<Node> vars;
    std::set<Node> boundVars;
    std::map<TypeNode, std::vector<Node>> selextIndexes;
    std::set<Node> arrays;
    std::set<Node> storeNodes;
    std::set<Node> selectNodes;
    std::set<Node> functionNodes;
    std::set<TypeNode> seqTypes;
    std::map<TypeNode, std::vector<Node>> seqNthIndexes;
    std::set<Node> seqs;
    std::set<TypeNode> typesSet;
    std::set<Node> seqNthNodes;
    std::map<int, TypeNode> typeNodeMapRev;
    std::map<TypeNode, int> typeNodeMap;
    std::map<TypeNode, std::set<int>> typeNodeIntSet;
    analyzeAssertions(assertionsToPreprocess, &constructoredTypes, &arrayTypes, &vars, &boundVars, &selextIndexes, &arrays, &storeNodes, &selectNodes, &functionNodes, &seqTypes, &seqNthIndexes, &seqs, &seqNthNodes, &typesSet, &typeNodeMap, &typeNodeMapRev, &typeNodeIntSet);

    Graph g;
    createGraph(&g, &typesSet, &typeNodeMap, &typeNodeMapRev);

    std::set<int> cycleNodes;
    nodeCycleDetector(&g, &cycleNodes, &typeNodeMapRev);

    // print the cycleNodes
    for (const auto& cycleNode : cycleNodes) {
        Assert(typeNodeMapRev.find(cycleNode) != typeNodeMapRev.end());
        Trace("nesteddtltag")  <<  "Cycle node type: "  <<  typeNodeMapRev[cycleNode]  <<  std::endl;
    }

    filterDT(&constructoredTypes, &arrayTypes, &vars, &selextIndexes, &arrays, &storeNodes, &selectNodes, &functionNodes, &seqTypes, &seqNthIndexes, &seqs, &cycleNodes, &typeNodeMap);
    
    // Create a map between the constructored types and arrays and the new types
    std::map<TypeNode, DType> mapDType;
    std::map<TypeNode, TypeNode> mapTypeNode;
    declareNewTypes(&constructoredTypes, &arrayTypes, &seqTypes, &mapDType, &mapTypeNode, nm);

    // Define the array types in the map
    defineArraySeqInMap(&mapDType, &mapTypeNode, &arrayTypes, &seqTypes, &selextIndexes, &seqNthIndexes, nm);

    // Define the constructored types in the map
    defineConstructoredInMap(&mapDType, &mapTypeNode, nm);

    // Resolve the map
    std::map<TypeNode, TypeNode> resolvedMap;
    createResolvedMap(&mapDType, nm, &resolvedMap);
    // print the resolvedMap
    for (const auto& pair : resolvedMap) {
        Trace("nesteddtltag")  <<  "createResolvedMap - Old type: "  <<  pair.first  <<  " New type: "  <<  pair.second  <<  std::endl;
        Trace("nesteddtltag")  <<  "createResolvedMap - New Dtype: "  <<  pair.second.getDType()  <<  std::endl;
    }

    // Create a map between the vars and the new vars
    std::map<Node, Node> varsMap;
    createVarsFuncsMap(&resolvedMap, &vars, nm, &varsMap, &functionNodes);
    // iterate over vars
    for (const auto& var : vars) {
        Assert(varsMap.find(var) != varsMap.end());
        Trace("nesteddtltag")  <<  "createVarsMap - Old var: "  <<  var  <<  " New var: "  <<  varsMap[var]  <<  std::endl;
        Trace("nesteddtltag")  <<  "createVarsMap - Old var type: "  <<  var.getType()  <<  " New var type: "  <<  varsMap[var].getType()  <<  std::endl;
    }

    // Create a map between the array types and the uninterpreted functions
    std::map<TypeNode, std::vector<Node>> ufArrays;
    createUFArrays(&resolvedMap, nm, &ufArrays);

    Trace("nesteddtltag")  <<  "after createUFArrays"  <<  std::endl;

    std::map<Node, Node> nodeMap;
    // Step 1: Precompute the "OR" vector
    std::set<int> shouldProcess;
    for (const auto& cycleNode : cycleNodes) {
        auto typeIt = typeNodeMapRev.find(cycleNode);
        Assert(typeIt != typeNodeMapRev.end());
        auto intSetIt = typeNodeIntSet.find(typeIt->second);
        Assert(intSetIt != typeNodeIntSet.end());
        
        shouldProcess.insert(intSetIt->second.begin(), intSetIt->second.end());
    }

    // Step 2: Iterate over the set shouldProcess and translate the assertions
    for(const auto& index : shouldProcess) {
        Node assertion = (*assertionsToPreprocess)[index];
        Node newAssertion = translateNode(assertion, varsMap, ufArrays, resolvedMap, nm, &nodeMap);
        assertionsToPreprocess->replace(index, newAssertion);
    }
    
    // Add the new assertions to the assertionsToPreprocess
    std::set<Node> newAssertions;
    addAssertionsSelect(&selectNodes, &cycleNodes, &typeNodeMap, &boundVars, &selextIndexes, nm, &newAssertions, &ufArrays, &nodeMap);
    addAssertionsArrays(&selectNodes, &boundVars, nm, &newAssertions, &ufArrays, &arrays, &nodeMap);
    addAssertionsStore(&selextIndexes, nm, &newAssertions, &ufArrays, &storeNodes, &nodeMap);
    addAssertionsSeqs(&seqs, nm, &newAssertions, &ufArrays, &seqs, &nodeMap);
    addAssertionsSeqNth(&seqNthNodes, &cycleNodes, &typeNodeMap , &seqNthIndexes, nm, &newAssertions, &ufArrays, &nodeMap);
    

    for (const auto& newAssertion : newAssertions) {
        assertionsToPreprocess->push_back(newAssertion);
        Trace("nesteddtltag")  <<  "New assertion: "  <<  newAssertion.toString()  <<  std::endl;
    }
    
    Trace("nesteddtltag")  <<  "___________________________"  <<  std::endl;
    // print assertions
    for (size_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i) {
        Trace("nesteddtltag")  <<  "(assert "  <<  (*assertionsToPreprocess)[i].toString()  << ")" << std::endl;
    }

    return PreprocessingPassResult::NO_CONFLICT;
}

void Nesteddtl::createGraph(Graph* g, std::set<TypeNode>* typesSet, std::map<TypeNode, int>* typeNodeMap, std::map<int, TypeNode>* typeNodeMapRev) {
    std::vector<Edge> edges; // Use vector to collect edges dynamically

    for (const auto& type : (*typesSet)) {
        if (type.isDatatype()) {
            const DType& dtype = type.getDType();
            size_t numConstructors = dtype.getNumConstructors();
            for (size_t i = 0; i < numConstructors; ++i) {
                const DTypeConstructor& constructor = dtype[i];
                for (size_t j = 0, n = constructor.getNumArgs(); j < n; ++j) {
                    TypeNode argType = constructor[j].getRangeType();
                    if (typeNodeMap->find(type) != typeNodeMap->end() && typeNodeMap->find(argType) != typeNodeMap->end()) {
                        edges.emplace_back((*typeNodeMap)[type], (*typeNodeMap)[argType]);
                    }
                }
            }
        } else if (type.isArray()) {
            TypeNode indexType = type.getArrayIndexType();
            TypeNode elementType = type.getArrayConstituentType();
            if (typeNodeMap->find(type) != typeNodeMap->end() && typeNodeMap->find(indexType) != typeNodeMap->end()) {
                edges.emplace_back((*typeNodeMap)[type], (*typeNodeMap)[indexType]);
            }
            if (typeNodeMap->find(type) != typeNodeMap->end() && typeNodeMap->find(elementType) != typeNodeMap->end()) {
                edges.emplace_back((*typeNodeMap)[type], (*typeNodeMap)[elementType]);
            }
        } else if (type.isSequence()) {
            TypeNode elementType = type.getSequenceElementType();
            if (typeNodeMap->find(type) != typeNodeMap->end() && typeNodeMap->find(elementType) != typeNodeMap->end()) {
                edges.emplace_back((*typeNodeMap)[type], (*typeNodeMap)[elementType]);
            }
        }
    }

    // Add edges to the graph
    for (const auto& edge : edges) {
        add_edge(edge.first, edge.second, *g);
    }
}


void Nesteddtl::nodeCycleDetector(Graph* g, std::set<int>* cycleTypes, std::map<int, TypeNode>* typeNodeMapRev) {
    // Create the reverse graph
    Graph reverse_g(num_vertices(*g));
    graph_traits<Graph>::edge_iterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(*g); ei != ei_end; ++ei) {
        add_edge(target(*ei, *g), source(*ei, *g), reverse_g);
    }

    // Compute the Strong Components (SCCs)
    std::vector<int> component(num_vertices(*g)), discover_time(num_vertices(*g));
    std::vector<default_color_type> color(num_vertices(*g));
    std::vector<Vertex> root(num_vertices(*g));
    int num = strong_components(
        *g, 
        make_iterator_property_map(component.begin(), get(vertex_index, *g)),
        root_map(make_iterator_property_map(root.begin(), get(vertex_index, *g))).
        color_map(make_iterator_property_map(color.begin(), get(vertex_index, *g))).
        discover_time_map(make_iterator_property_map(discover_time.begin(), get(vertex_index, *g)))
    );

    std::vector<int> component_sizes(num, 0);
    for (int comp_id : component) {
        ++component_sizes[comp_id];
    }


    // Process each SCC
    std::vector<bool> visited(num_vertices(*g), false);
    for (size_t i = 0; i < component.size(); ++i) {
        if (component_sizes[component[i]] > 1) {
            bool hasArrayType = false;
            int startNode = -1;
            for (size_t j = 0; j < component.size(); ++j) {
                if (component[j] == component[i] && (typeNodeMapRev->at(j).isArray() || typeNodeMapRev->at(j).isSequence())) {
                    hasArrayType = true;
                    startNode = j;
                    break;
                }
            }
            if (hasArrayType) {
                // Perform DFS from startNode
                std::stack<int> stack;
                stack.push(startNode);

                while (!stack.empty()) {
                    int node = stack.top();
                    stack.pop();

                    if (!visited[node]) {
                        visited[node] = true;
                        cycleTypes->insert(node);

                        // add the children of the current node to the stack
                        graph_traits<Graph>::adjacency_iterator ai, ai_end;
                        for (boost::tie(ai, ai_end) = adjacent_vertices(node, reverse_g); ai != ai_end; ++ai) {
                            stack.push(*ai);
                        }
                    }
                }
            }
        }
    }
}

void Nesteddtl::analyzeAssertions(AssertionPipeline* assertionsToPreprocess, std::set<TypeNode>* constructoredTypes, std::set<TypeNode>* arrayTypes, std::set<Node>* vars, std::set<Node>* boundVars, std::map<TypeNode, std::vector<Node>>* selectAssertions, std::set<Node>* arrays, std::set<Node>* storeNodes, std::set<Node>* selectNodes, std::set<Node>* functionNodes, std::set<TypeNode>* seqTypes, std::map<TypeNode, std::vector<Node>>* seqNthAssertions, std::set<Node>* seqs, std::set<Node>* seqNthNodes, std::set<TypeNode>* typesSet, std::map<TypeNode, int>* typeNodeMap, std::map<int, TypeNode>* typeNodeMapRev, std::map<TypeNode, std::set<int>>* typeNodeIntSet) {
    std::stack<Node> stack;
    std::set<Node> visitedNodes;
    std::map<TypeNode, std::set<Node>> selectAssertionsSet;
    std::map<TypeNode, std::set<Node>> seqNthAssertionsSet;
    size_t assertions_size = assertionsToPreprocess->size();
    for (size_t i = 0; i < assertions_size; ++i) {
        stack.push((*assertionsToPreprocess)[i]);

        while (!stack.empty()) {
            Node& current = stack.top();
            stack.pop();

            const auto& type = current.getType();
            if (typesSet->find(type) == typesSet->end()){
                typeNodeMap->insert(std::pair<TypeNode, int>(type, typesSet->size()));
                typeNodeMapRev->insert(std::pair<int, TypeNode>(typeNodeMapRev->size(), type));

                std::set<int> intSet;
                intSet.insert(i);
                typeNodeIntSet->insert(std::pair<TypeNode, std::set<int>>(type, intSet));

                typesSet->emplace(type);
            } else{
                typeNodeIntSet->at(type).insert(i);
            }

            // Check if the node has already been visitedNodes
            if (visitedNodes.find(current) != visitedNodes.end()) {
                continue; // Skip the rest of the loop if the node is already visitedNodes
            }
            visitedNodes.insert(current); // Mark the current node as visitedNodes

            if (current.isVar()){
                vars->emplace(current);
            }
            if (current.isVar() && (current.getKind() == Kind::BOUND_VARIABLE)){
                boundVars->emplace(current);
            }
            if (type.isDatatype()) {
                constructoredTypes->emplace(type);
            }
            if (type.isArray()) {
                arrayTypes->emplace(type);
                arrays->insert(current);
            }
            if (type.isSequence()) {
                seqTypes->emplace(type);
                seqs->insert(current);
            }
            
            if (current.getKind() == Kind::SELECT) {
                selectNodes->insert(current);
            } 
            if (current.getKind() == Kind::SEQ_NTH) {
                seqNthNodes->insert(current);
            }
            if (current.getKind() == Kind::STORE){
                TypeNode arrayType = current[0].getType();
                TypeNode indexType = current[1].getType();
                // check if the arrayType or indexType is in the selectAssertionsSet
                storeNodes->insert(current);
            }
            if (current.getKind() == Kind::APPLY_UF){
                if (current.getOperator().getType().isFunction()){
                    functionNodes->insert(current.getOperator());
                }
            }

            //iterate over the children of the current node
            for (const auto& child : current) {
                stack.push(child);
            }
        }
    }
    for (const Node& selectNode : (*selectNodes)) {
        Node array = selectNode[0];
        Node index = selectNode[1];
        TypeNode arrayType = array.getType();
        selectAssertionsSet[arrayType].insert(index);
    } 
    for (const Node& seqNthNode : (*seqNthNodes)) {
        Node seq = seqNthNode[0];
        Node index = seqNthNode[1];
        TypeNode seqType = seq.getType();
        seqNthAssertionsSet[seqType].insert(index);
    } 
    for (const Node& storeNode : (*storeNodes)) {
        Node array = storeNode[0];
        Node index = storeNode[1];
        TypeNode arrayType = array.getType();
        selectAssertionsSet[arrayType].insert(index);
    } 
    // print the selectAssertions
    for (const auto& pair : selectAssertionsSet) {
        Trace("nesteddtltag")  <<  "Type: "  <<  pair.first  <<  std::endl;
        for (const auto& selectNode : pair.second) {
            Trace("nesteddtltag")  <<  "Select node: "  <<  selectNode  <<  std::endl;
        }
    }
    // convert the selectAssertions to a map of TypeNode to vector of Node
    for (const auto& pair : selectAssertionsSet) {
        std::vector<Node> selectNodesVector;
        for (const auto& selectNode : pair.second) {
            selectNodesVector.push_back(selectNode);
        }
        (*selectAssertions).insert(std::pair<TypeNode, std::vector<Node>>(pair.first, selectNodesVector));
    }
    for (const auto& pair : seqNthAssertionsSet) {
        std::vector<Node> seqNthVector;
        for (const auto& seqNthNode : pair.second) {
            seqNthVector.push_back(seqNthNode);
        }
        (*seqNthAssertions).insert(std::pair<TypeNode, std::vector<Node>>(pair.first, seqNthVector));
    }
}

void Nesteddtl::filterDT(std::set<TypeNode>* constructoredTypes, std::set<TypeNode>* arrayTypes, std::set<Node>* vars, std::map<TypeNode, std::vector<Node>>* selectAssertions, std::set<Node>* arrays, std::set<Node>* storeNodes, std::set<Node>* selectNodes, std::set<Node>* functionNodes, std::set<TypeNode>* seqTypes, std::map<TypeNode, std::vector<Node>>* seqNthAssertions, std::set<Node>* seqs, std::set<int>* cycleNodes, std::map<TypeNode, int>* typeNodeMap){
    // remove the types that are not in cycleNodes from constructoredTypes
    for (auto it = constructoredTypes->begin(); it != constructoredTypes->end(); ) {
        const auto& type = *it;
        if (cycleNodes->find(typeNodeMap->at(type)) == cycleNodes->end()) {
            it = constructoredTypes->erase(it);
        } else {
            ++it;
        }
    }

    for (auto it = arrayTypes->begin(); it != arrayTypes->end(); ) {
        const auto& type = *it;
        if (cycleNodes->find(typeNodeMap->at(type)) == cycleNodes->end()) {
            it = arrayTypes->erase(it);
        } else {
            ++it;
        }
    }

    for (auto it = vars->begin(); it != vars->end(); ) {
        const auto& var = *it;
        if (cycleNodes->find(typeNodeMap->at(var.getType())) == cycleNodes->end()) {
            it = vars->erase(it);
        } else {
            ++it;
        }
    }

    for (auto it = selectAssertions->begin(); it != selectAssertions->end(); ) {
        const auto& selectAssertion = *it;
        if (cycleNodes->find(typeNodeMap->at(selectAssertion.first)) == cycleNodes->end()) {
            it = selectAssertions->erase(it);
        } else {
            ++it;
        }
    }

    for (auto it = arrays->begin(); it != arrays->end(); ) {
        const auto& array = *it;
        if (cycleNodes->find(typeNodeMap->at(array.getType())) == cycleNodes->end()) {
            it = arrays->erase(it);
        } else {
            ++it;
        }
    }

    for (auto it = storeNodes->begin(); it != storeNodes->end(); ) {
        const auto& storeNode = *it;

        TypeNode arrayType = storeNode[0].getType();
        Assert(typeNodeMap->find(arrayType) != typeNodeMap->end());

        if (cycleNodes->find(typeNodeMap->at(arrayType)) != cycleNodes->end()) {
            ++it;
            continue;
        }

        TypeNode indexType = storeNode[1].getType();
        Assert(typeNodeMap->find(indexType) != typeNodeMap->end());

        if (cycleNodes->find(typeNodeMap->at(indexType)) != cycleNodes->end()) {
            ++it;
            continue;
        }

        // Correctly update 'it' after erasing the current element
        it = storeNodes->erase(it);
    }

    for (auto it = selectNodes->begin(); it != selectNodes->end(); ) {
        const auto& selectNode = *it;

        TypeNode arrayType = selectNode[0].getType();
        Assert (typeNodeMap->find(arrayType) != typeNodeMap->end());

        if (cycleNodes->find(typeNodeMap->at(arrayType)) != cycleNodes->end()){
            ++it;
            continue;
        }

        TypeNode indexType = selectNode[1].getType();
        Assert (typeNodeMap->find(indexType) != typeNodeMap->end());

        if (cycleNodes->find(typeNodeMap->at(indexType)) != cycleNodes->end()){
            ++it;
            continue;
        }

        // Correctly update 'it' to the next valid iterator after erasing
        it = selectNodes->erase(it);
    }

    // remove the selectNodes that are not in cycleNodes from selectNodes
    for (auto it = functionNodes->begin(); it != functionNodes->end(); ) {
        const auto& functionNode = *it;

        TypeNode functionType = functionNode.getType();
        TypeNode functionOutput = functionType.getRangeType();
        Assert(typeNodeMap->find(functionOutput) != typeNodeMap->end());

        if (cycleNodes->find(typeNodeMap->at(functionOutput)) != cycleNodes->end()) {
            ++it;
            continue; // Skip to the next iteration, don't break the loop
        }

        std::vector<TypeNode> functionInput = functionType.getArgTypes();
        for (const auto& input : functionInput) {
            Assert(typeNodeMap->find(input) != typeNodeMap->end());
            if (cycleNodes->find(typeNodeMap->at(input)) != cycleNodes->end()) {
                ++it;
                break; // Break from the inner loop, not the outer loop
            }
        }

        it = functionNodes->erase(it);
    } 
    for (auto it = seqTypes->begin(); it != seqTypes->end(); ) {
        const auto& seqType = *it;
        Assert(typeNodeMap->find(seqType) != typeNodeMap->end());
        if (cycleNodes->find(typeNodeMap->at(seqType)) == cycleNodes->end()) {
            it = seqTypes->erase(it);
        } else {
            ++it;
        }
    }
    for (auto it = seqNthAssertions->begin(); it != seqNthAssertions->end(); ) {
        const auto& seqNthAssertion = *it;
        Assert(typeNodeMap->find(seqNthAssertion.first) != typeNodeMap->end());
        if (cycleNodes->find(typeNodeMap->at(seqNthAssertion.first)) == cycleNodes->end()) {
            it = seqNthAssertions->erase(it);
        } else {
            ++it;
        }
    }
    for (auto it = seqs->begin(); it != seqs->end(); ) {
        const auto& seq = *it;
        Assert(typeNodeMap->find(seq.getType()) != typeNodeMap->end());
        if (cycleNodes->find(typeNodeMap->at(seq.getType())) == cycleNodes->end()) {
            it = seqs->erase(it);
        } else {
            ++it;
        }
    }
}


void Nesteddtl::declareNewTypes(std::set<TypeNode>* constructoredTypes, std::set<TypeNode>* arrayTypes, std::set<TypeNode>* seqTypes, std::map<TypeNode, DType>* mapDType, std::map<TypeNode, TypeNode>* mapTypeNode, NodeManager* nm){
    std::stringstream ss;
    TypeNode unresSort;
    // Iterate over constructoredTypes
    for (const auto& constructoredType : (*constructoredTypes)) {
        ss.str("");
        ss  <<  constructoredType  <<  "_rc";
        // Declare a new type for each constructoredType
        DType newDType(ss.str());
        (*mapDType).insert(std::pair<TypeNode, DType>(constructoredType, newDType));

        unresSort = nm->mkUnresolvedDatatypeSort(ss.str());
        (*mapTypeNode).insert(std::pair<TypeNode, TypeNode>(constructoredType, unresSort));

    }

    for (const auto& arrayType : (*arrayTypes)) {
        ss.str("");
        ss  <<  "Array_["  <<  arrayType.getArrayIndexType()  <<  "_"  <<  arrayType.getArrayConstituentType()  <<  "]_rc";
        // Declare a new type for each arrayType
        DType newDType(ss.str());
        (*mapDType).insert(std::pair<TypeNode, DType>(arrayType, newDType));

        unresSort = nm->mkUnresolvedDatatypeSort(ss.str());
        (*mapTypeNode).insert(std::pair<TypeNode, TypeNode>(arrayType, unresSort));
    }

    for (const auto& seqType : (*seqTypes)) {
        ss.str("");
        ss  <<  "Seq_"  <<  seqType.getSequenceElementType()  <<  "_rc";
        // Declare a new type for each arrayType
        DType newDType(ss.str());
        (*mapDType).insert(std::pair<TypeNode, DType>(seqType, newDType));

        unresSort = nm->mkUnresolvedDatatypeSort(ss.str());
        (*mapTypeNode).insert(std::pair<TypeNode, TypeNode>(seqType, unresSort));
    }
}


void Nesteddtl::defineArraySeqInMap(std::map<TypeNode, DType>* mapDType, std::map<TypeNode, TypeNode>* mapTypeNode, std::set<TypeNode>* arrayTypes, std::set<TypeNode>* seqTypes, std::map<TypeNode, std::vector<Node>>* selectAssertions, std::map<TypeNode, std::vector<Node>>* seqNthAssertions, NodeManager* nm){
    std::stringstream ss;
    // Iterate over arrayTypes
    for (const auto& arrayType : (*arrayTypes)) {
        // Get the arrayType's DType from the mapDType
        auto it = (*mapDType).find(arrayType);
        Assert(it != (*mapDType).end());
        // The key exists in the mapDType, you can safely access it
        DType& newDType = it->second;
        // Get the DType of the arrayType
        TypeNode indexType = arrayType.getArrayIndexType();
        TypeNode elementType = arrayType.getArrayConstituentType();
        // Add an empty constructor
        ss.str("");
        //ss  <<  "nil_"  <<  indexType  <<  "_"  <<  elementType;
        //std::shared_ptr<DTypeConstructor> nil = std::make_shared<DTypeConstructor>(ss.str());
        //newDType.addConstructor(nil);
        // Add a constructor for the array's elements
        std::shared_ptr<DTypeConstructor> cons = std::make_shared<DTypeConstructor>("cons");
        // add the id as an argument to the constructor
        cons->addArg("id", nm->integerType());
        // Iterate over the select assertions of the arrayType
        TypeNode newElementType = convertTypeNode(elementType, mapTypeNode);
        auto it2 = (*selectAssertions).find(arrayType);
        if (it2 != (*selectAssertions).end()) {
            for (size_t i=0, element_num = it2->second.size(); i < element_num; i++){
                // Add new field for each index
                ss.str("");;
                ss  <<  "index_"  <<  i;
                cons->addArg(ss.str(), newElementType);
            }
        }       
        newDType.addConstructor(cons);
        // Insert the new type into the mapDType
        (*mapDType).insert(std::pair<TypeNode, DType>(arrayType, newDType));
    }

    // Iterate over arrayTypes
    for (const auto& seqType : (*seqTypes)) {
        // Get the arrayType's DType from the mapDType
        auto it = (*mapDType).find(seqType);
        Assert(it != (*mapDType).end());
        // The key exists in the mapDType, you can safely access it
        DType& newDType = it->second;
        // Get the DType of the arrayType
        TypeNode elementType = seqType.getSequenceElementType();
        TypeNode newElementType = convertTypeNode(elementType, mapTypeNode);
        // Add an empty constructor
        //ss.str("");
        //ss  <<  "nil_"  <<  newElementType;
        //std::shared_ptr<DTypeConstructor> nil = std::make_shared<DTypeConstructor>(ss.str());
        //newDType.addConstructor(nil);
        // Add a constructor for the array's elements
        std::shared_ptr<DTypeConstructor> cons = std::make_shared<DTypeConstructor>("cons");
        // add the id as an argument to the constructor
        cons->addArg("id", nm->integerType());
        
        auto it2 = (*seqNthAssertions).find(seqType);
        if (it2 != (*seqNthAssertions).end()) {
            for (size_t i=0, element_num = it2->second.size(); i < element_num; i++){
                // Add new field for each index
                ss.str("");;
                ss  <<  "index_"  <<  i;
                cons->addArg(ss.str(), newElementType);
            }
        }       
        newDType.addConstructor(cons);
        // Insert the new type into the mapDType
        (*mapDType).insert(std::pair<TypeNode, DType>(seqType, newDType));
    }
}

void Nesteddtl::defineConstructoredInMap(std::map<TypeNode, DType>* mapDType, std::map<TypeNode, TypeNode>* mapTypeNode, NodeManager* nm){
    std::stringstream ss;
    // Iterate over mapDType
    for (const auto& pair : (*mapDType)) {
        // Get the typeNode
        const TypeNode& typeNode = pair.first;
        // Check if typeNode is in an array type
        if (typeNode.isArray() || typeNode.isSequence()){
            continue;
        }
        // Get the DType
        auto it = (*mapDType).find(typeNode);
        Assert(it != (*mapDType).end());
        // The key exists in the mapDType, you can safely access it
        DType& dtype = it->second;
        // Get the DType of the typeNode
        const DType& oldDtype  = typeNode.getDType();
        // Get the number of constructors
        size_t numConstructors = oldDtype.getNumConstructors();
        // Iterate over the constructors
        for (size_t i = 0; i < numConstructors; ++i) {
            // Get the constructor
            const DTypeConstructor& constructor = oldDtype[i];
            // Get the name of the constructor
            ss.str("");
            ss  <<  constructor.getName()  <<  "_rc";
            // Create a new constructor
            std::shared_ptr<DTypeConstructor> newConstructor = std::make_shared<DTypeConstructor>(ss.str());
            // Get the number of arguments
            size_t numArgs = constructor.getNumArgs();
            // Iterate over the arguments
            for (size_t j = 0; j < numArgs; ++j) {
                // Get the selector
                const DTypeSelector& selector = constructor[j];
                // Get the name of the selector
                ss.str("");
                ss  <<  selector.getName()  <<  "_rc";
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

void Nesteddtl::createResolvedMap(std::map<TypeNode, DType>* mapDType, NodeManager* nm, std::map<TypeNode, TypeNode>* resolvedMap){
    std::vector<DType> datatypes;
    std::vector<TypeNode> oldTypes;
    for (const auto& pair : (*mapDType)) {
        oldTypes.push_back(pair.first);
        datatypes.push_back(pair.second);
    }
    // Using the mkMutualDatatypeTypes function to create the new types
    std::vector<TypeNode> resolvedTypes = nm->mkMutualDatatypeTypes(datatypes);

    // Create the map resolvedMap between the old types and the resolvedTypes
    for (size_t i = 0, n = oldTypes.size(); i < n; ++i) {
        (*resolvedMap).insert(std::pair<TypeNode, TypeNode>(oldTypes[i], resolvedTypes[i]));
    }
}

TypeNode Nesteddtl::convertTypeNode(TypeNode type, std::map<TypeNode, TypeNode>* typeMap) {
    // check if the type is in the resolvedMap
    if (typeMap->find(type) != typeMap->end()){
        return (*typeMap)[type];
    }
    return type;
}

void Nesteddtl::createVarsFuncsMap(std::map<TypeNode, TypeNode>* resolvedMap, std::set<Node>* vars, NodeManager* nm, std::map<Node, Node>* varsMap, std::set<Node>* functionNodes){
    // Iterate over vars
    Node newVar;
    TypeNode newType;
    std::stringstream newName;
    SkolemManager* sm = nm->getSkolemManager();

    for (const auto& var : (*vars)) {
        newName.str("");
        newName  <<  var.toString()  <<  "_rc";
        newType = convertTypeNode(var.getType(), resolvedMap);
        newVar = sm->mkDummySkolem(newName.str(), newType);
        (*varsMap).insert(std::pair<Node, Node>(var, newVar));
        Trace("nesteddtltag")  <<  "Old var: "  <<  var  <<  " Old type: "  <<  var.getType()  <<  " New var: "  <<  newVar  <<  " New type: "  <<  newType << std::endl;
    }

    // Iterate over functionNodes
    for (const auto& functionNode : (*functionNodes)) {
        // get the functionNode name
        newName.str("");
        newName  <<  functionNode.toString()  <<  "_rc";
        TypeNode functionType = functionNode.getType();
        // get the functionNode input
        std::vector<TypeNode> functionInput = functionType.getArgTypes();
        // get the functionNode output
        TypeNode functionOutput = functionType.getRangeType();
        // convert the functionNode input
        std::vector<TypeNode> newFunctionInput;
        for (const auto& input : functionInput) {
            newType = convertTypeNode(input, resolvedMap);
            newFunctionInput.push_back(newType);
        }
        // convert the functionNode output
        TypeNode newFunctionOutput = convertTypeNode(functionOutput, resolvedMap);
        TypeNode newFunctionType = nm->mkFunctionType(newFunctionInput, newFunctionOutput);
        Node newFunctionNode = sm->mkDummySkolem(newName.str(), newFunctionType);
        (*varsMap).insert(std::pair<Node, Node>(functionNode, newFunctionNode));
        Trace("nesteddtltag")  <<  " New functionNode: "  <<  newFunctionNode  <<  " New type: "  <<  newFunctionType << std::endl;
    }

    // iterate over resolvedMap
    for (const auto& pair : (*resolvedMap)) {
        // Get the typeNode
        const TypeNode& oldType = pair.first;
        const TypeNode& newResolvedType = pair.second;
        // Check if typeNode is in an array type
        if (oldType.isArray() || oldType.isSequence()){
            continue;
        }
        // Get the DType
        DType oldDType = oldType.getDType();
        DType newDType = newResolvedType.getDType();
        // Get the number of constructors
        size_t oldNumConstructors = oldDType.getNumConstructors();
        Assert(oldNumConstructors == newDType.getNumConstructors());
        // Iterate over the constructors
        for (size_t i = 0; i < oldNumConstructors; ++i) {
            // Get the constructor
            const DTypeConstructor& oldConstructor = oldDType[i];
            const DTypeConstructor& newConstructor = newDType[i];
            // Get the name of the constructor
            
            TNode oldConstructorNode = oldConstructor.getConstructor();
            TNode newConstructorNode = newConstructor.getConstructor();
            (*varsMap).insert(std::pair<Node, Node>(oldConstructorNode, newConstructorNode));
            // Get the number of arguments
            size_t oldNumArgs = oldConstructor.getNumArgs();
            Assert(oldNumArgs == newConstructor.getNumArgs());
            // Iterate over the arguments
            for (size_t j = 0; j < oldNumArgs; ++j) {
                (*varsMap).insert(std::pair<Node, Node>(oldConstructor.getSelector(j), newConstructor.getSelector(j)));
            }
        }
    }
}

void Nesteddtl::createUFArrays(std::map<TypeNode, TypeNode>* map, NodeManager* nm, std::map<TypeNode, std::vector<Node>>* ufArrays){
    SkolemManager* sm = nm->getSkolemManager();
    // Iterate over map
    for (const auto& pair : (*map)) {
        // Get the typeNode
        const TypeNode& oldArrayType = pair.first;
        // Check if typeNode is in an array type
        if (oldArrayType.isArray()){
            const TypeNode& consType = pair.second;
            TypeNode indexType = oldArrayType.getArrayIndexType();
            TypeNode elementType = oldArrayType.getArrayConstituentType();
            // create a new array type from the oldIndexType and oldElementType
            indexType = convertTypeNode(indexType, map);
            elementType = convertTypeNode(elementType, map);
            TypeNode newArrayType = nm->mkArrayType(indexType, elementType);
            
            // Create a old to new
            std::string consToArrName = consType.toString() + "_0";
            Node consToArr = sm->mkDummySkolem(consToArrName, nm->mkFunctionType(consType, newArrayType));
            // Create a new to old
            std::string arrToOldName = consType.toString() + "_1";
            Node arrToCons = sm->mkDummySkolem(arrToOldName, nm->mkFunctionType(newArrayType, consType));
            // Create a vector of the two uninterpreted functions
            std::vector<Node> ufArray;
            ufArray.push_back(consToArr);
            ufArray.push_back(arrToCons);

            // Insert the new type into the map
            (*ufArrays).insert(std::pair<TypeNode, std::vector<Node>>(oldArrayType, ufArray));
        } else if (oldArrayType.isSequence()){
            const TypeNode& consType = pair.second;
            TypeNode elementType = oldArrayType.getSequenceElementType();
            // create a new array type from the oldIndexType and oldElementType
            elementType = convertTypeNode(elementType, map);
            TypeNode newSeqType = nm->mkSequenceType(elementType);
            
            // Create a old to new
            std::string consToArrName = consType.toString() + "_0";
            Node consToArr = sm->mkDummySkolem(consToArrName, nm->mkFunctionType(consType, newSeqType));
            // Create a new to old
            std::string arrToOldName = consType.toString() + "_1";
            Node arrToCons = sm->mkDummySkolem(arrToOldName, nm->mkFunctionType(newSeqType, consType));
            // Create a vector of the two uninterpreted functions
            std::vector<Node> ufArray;
            ufArray.push_back(consToArr);
            ufArray.push_back(arrToCons);

            // Insert the new type into the map
            (*ufArrays).insert(std::pair<TypeNode, std::vector<Node>>(oldArrayType, ufArray));
        }
        
    }
    // print the ufArrays
    for (const auto& pair : (*ufArrays)) {
        Trace("nesteddtltag")  <<  "createUFArrays: Old array type: "  <<  pair.first  <<  std::endl;
        Trace("nesteddtltag")  <<  "createUFArrays: cons to arr: "  <<  pair.second[0]  << " type: " << pair.second[0].getType() << std::endl;
        Trace("nesteddtltag")  <<  "createUFArrays: arr to cons: "  <<  pair.second[1]  << " type: " << pair.second[1].getType() << std::endl;
    }
}

Node Nesteddtl::translateNode(const Node node, std::map<Node, Node> varsMap, std::map<TypeNode, std::vector<Node>> ufArrays, std::map<TypeNode, TypeNode> resolvedMap, NodeManager* nm, std::map<Node, Node>* nodeMap){
    // check if node is in nodeMap, if so return its value
    if (nodeMap->find(node) != nodeMap->end()){
        return (*nodeMap)[node];
    }
    // Use node traversal to iterate the subnodes of node
    NodeDfsIterable nodeDfsIterable(node);
    for (TNode current : nodeDfsIterable){
        // print the current node and its type
        Trace("nesteddtltag")  <<  "Current node: "  <<  current  <<  ". Current node's type: "  <<  current.getType()  <<  ". Current node's kind: "  <<  current.getKind()  <<  std::endl;
        if (nodeMap->find(current) != nodeMap->end()){
            Trace("nesteddtltag")  <<  "already know: " << current  <<  std::endl;
            continue;
        }
        if (current.hasOperator()){
            Trace("nesteddtltag")  <<  "Inside the hasOperator"  <<  std::endl;
            translateOperator(current, nm, nodeMap, &varsMap);            
        } else{
            Trace("nesteddtltag")  <<  "Inside the isVar"  <<  std::endl;
            translateVar(current, nodeMap, &varsMap);
        }

        // check if the type of (*nodeMap)[current] is not an array         
        Assert(nodeMap->find(current) != nodeMap->end()); 
        Node n = (*nodeMap)[current]; 
        bool checkArray =  current.getType().isArray() && !n.getType().isArray();
        bool checkSeq =  current.getType().isSequence() && !n.getType().isSequence();
        if (checkArray || checkSeq){
            // find current in ufArrays
            Node consToNew = ufArrays[current.getType()][0];
            TypeNode t2 = consToNew.getType().getArgTypes()[0];
            // check if t1 is equal to t2
            assert (n.getType() == t2);
            Node consToNewApplication = nm->mkNode(Kind::APPLY_UF, consToNew, n);
            (*nodeMap)[current] = consToNewApplication;
        }
        
        // print the new node and its translation
        Trace("nesteddtltag")  <<  "Node: "  <<  current  <<  " translation: "  << (*nodeMap)[current]  <<  std::endl;
        Trace("nesteddtltag")  <<  "Node's type: "  <<  current.getType()  <<  " translation's type: "  << (*nodeMap)[current].getType() << " translation's kind: "  << (*nodeMap)[current].getKind()  <<  std::endl;
    }

    return (*nodeMap)[node];
}

void Nesteddtl::translateVar(Node current, std::map<Node, Node>* nodeMap, std::map<Node, Node>* varsMap) {
    // check if the current node is in the varsMap
    if (varsMap->find(current) != varsMap->end()){
        Node n =  (*varsMap)[current];
        nodeMap->insert(std::pair<Node, Node>(current, n));
    } else{
        nodeMap->insert(std::pair<Node, Node>(current, current));
    }
}

void Nesteddtl::translateOperator(Node current, NodeManager* nm, std::map<Node, Node>* nodeMap,  std::map<Node, Node>* varsMap){
    Node translatedChild;
    // get the operator
    Node operatorNode = current.getOperator();
    auto it = (*varsMap).find(operatorNode);
    if (it != (*varsMap).end()) {
        operatorNode = it->second;
    }
    std::vector<TNode> newChildren;
    if (current.getKind() == Kind::BOUND_VAR_LIST) {
        for (size_t j = 0; j < current.getNumChildren(); ++j) {
            translatedChild = (*nodeMap)[current[j]];
            if (translatedChild.getKind() == Kind::APPLY_UF){
                translatedChild = translatedChild[0];
            }
            newChildren.push_back(translatedChild);
            Trace("nesteddtltag")  <<  "translatedChild: " << j <<  " "<< translatedChild << std::endl;
        }
    }
    else{
        for (size_t j = 0; j < current.getNumChildren(); ++j) {
            newChildren.push_back((*nodeMap)[current[j]]);
        }
    }
    std::set<Kind> kindSet = {Kind::APPLY_SELECTOR, Kind::APPLY_CONSTRUCTOR, Kind::APPLY_UF};
    // check if the current node is an kindSet
    if (kindSet.find(current.getKind()) != kindSet.end()){
        newChildren.insert(newChildren.begin(), operatorNode);
        Node newNode = nm->mkNode(current.getKind(), newChildren);
        nodeMap->insert(std::pair<Node, Node>(current, newNode));
    } else {
        Node newNode = nm->mkNode(operatorNode, newChildren);
        nodeMap->insert(std::pair<Node, Node>(current, newNode));
    }
}   

void Nesteddtl::addAssertionsSelect(std::set<Node>* selectNodes, std::set<int>* cycleNodes, std::map<TypeNode, int>* typeNodeMap, std::set<Node>* boundVars, std::map<TypeNode, std::vector<Node>>* arrayIndexes, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::map<Node, Node>* nodeMap){
    Node selector_application, assertion, selector, newSelectNode, originalArrayNode, newArrayNode, originalIndexNode, arrToCons, arrToConsApplication;
    // iterate over the selectNodes
    for (const auto& originalSelectNode : (*selectNodes)){ 
        originalIndexNode = originalSelectNode[1];
        originalArrayNode = originalSelectNode[0];
        if (boundVars->find(originalArrayNode) != boundVars->end()){
            continue;
        }

        // check if originalSelectNode is in nodeMap
        Assert((nodeMap->find(originalSelectNode) != nodeMap->end()));

        newSelectNode = (*nodeMap)[originalSelectNode];
        newArrayNode = newSelectNode[0];
        if (boundVars->find(originalArrayNode) != boundVars->end()){
            continue;
        }
        if (!newArrayNode.getType().isArray()){
            newArrayNode = newArrayNode[0];
        }
        if (ufArrays->find(originalArrayNode.getType()) == ufArrays->end()){
            continue;
        }

        arrToCons = (*ufArrays)[originalArrayNode.getType()][1];
        arrToConsApplication = nm->mkNode(Kind::APPLY_UF, arrToCons, newArrayNode);
        // insert the equality between the recursive element and the indexed element
        const DType& newDType = arrToConsApplication.getType().getDType();
        // iterate over the constructors    
        for (size_t i = 0, n = newDType.getNumConstructors(); i < n; ++i) {
            const DTypeConstructor& cons = newDType[i];
            if (cons.getNumArgs() == 0) {
                continue;
            }
            if (newArrayNode.getKind() == Kind::APPLY_UF){
                Node consToArrFunc = (*ufArrays)[originalArrayNode.getType()][0];
                // check if the function is consToArrFunc
                if (newArrayNode.getOperator() == consToArrFunc){      
                    arrToConsApplication = newArrayNode[0];
                }
            }
        
            std::vector<Node> oldIndexes = (*arrayIndexes)[originalArrayNode.getType()];
            for (size_t j = 0; j < oldIndexes.size(); j++){
                if (oldIndexes[j] == originalIndexNode){
                    selector = cons[j+1].getSelector();
                    selector_application = nm->mkNode(Kind::APPLY_SELECTOR, selector, arrToConsApplication);
                    if (newSelectNode.getType().isArray() && !selector_application.getType().isArray()){
                        // find current in ufArrays
                        Assert(ufArrays->find(originalSelectNode.getType()) != ufArrays->end()); 
                        Node consToNew = (*ufArrays)[originalSelectNode.getType()][0];
                        TypeNode t2 = consToNew.getType().getArgTypes()[0];
                        // check if t1 is equal to t2
                        assert (selector_application.getType() == t2);
                        selector_application = nm->mkNode(Kind::APPLY_UF, consToNew, selector_application);
                    }
                    assertion = nm->mkNode(Kind::EQUAL, selector_application, newSelectNode);
                    if (selector_application.hasOperator() && newSelectNode.hasOperator()){
                        if (selector_application.getOperator() == newSelectNode.getOperator()){
                            assertion = nm->mkNode(Kind::EQUAL, selector_application[0], newSelectNode[0]);
                        }
                    }
                    newAssertions->insert(assertion);
                    break;
                }
            }      
        }        
    } 
}



void Nesteddtl::addAssertionsArrays(std::set<Node>* selectNodes, std::set<Node>* boundVars, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::set<Node>* arrays, std::map<Node, Node>* nodeMap){
    Node first, assertion, notAssertion, newArrayNode, consToArrFunc, arrToConsFunc, applyArrToCons;
    TNode opNode;
        // iterate over the arrays
    for (const auto& originalArray : (*arrays)) {
        if (boundVars->find(originalArray) != boundVars->end()){
            continue;
        }
        Assert(nodeMap->find(originalArray) != nodeMap->end());
        newArrayNode = (*nodeMap)[originalArray];
        // check if the newArrayNode is a UF application
        if (newArrayNode.getKind() == Kind::APPLY_UF){
            consToArrFunc = (*ufArrays)[originalArray.getType()][0];
            arrToConsFunc = (*ufArrays)[originalArray.getType()][1];
            // check if the function is consToArrFunc
            if (newArrayNode.getOperator() == consToArrFunc){      
                // insert that application of array2cons is consistent   
                applyArrToCons = nm->mkNode(Kind::APPLY_UF, arrToConsFunc, newArrayNode);

                assertion = nm->mkNode(Kind::EQUAL, newArrayNode[0], applyArrToCons);
                newAssertions->insert(assertion);

                // insert it is not nil
                const DType& newDType = applyArrToCons.getType().getDType();
                size_t numConstructors = newDType.getNumConstructors();
                for (size_t i = 0; i < numConstructors; ++i) {
                    const DTypeConstructor& constructor = newDType[i];
                    if (constructor.getNumArgs() == 0) {
                        // create a TNode from the constructor
                        opNode = constructor.getConstructor();
                        first = nm->mkNode(Kind::APPLY_CONSTRUCTOR, opNode);
                        notAssertion = nm->mkNode(Kind::NOT, nm->mkNode(Kind::EQUAL, newArrayNode[0], first));
                        newAssertions->insert(notAssertion);
                        break;
                    }
                }
            }
        }
    }  
}

void Nesteddtl::addAssertionsSeqNth(std::set<Node>* seqNthNodes, std::set<int>* cycleNodes, std::map<TypeNode, int>* typeNodeMap, std::map<TypeNode, std::vector<Node>>* seqNthIndexes, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::map<Node, Node>* nodeMap){
    Node selector_application, assertion, selector, newSeqNthNode, originalSeqNode, newSeqNode, originalIndexNode, arrToCons, arrToConsApplication;
    // iterate over the selectNodes
    for (const auto& originalSeqNthNode : (*seqNthNodes)){  
        originalIndexNode = originalSeqNthNode[1];
        originalSeqNode = originalSeqNthNode[0];
        if (cycleNodes->find((*typeNodeMap)[originalSeqNode.getType()]) == cycleNodes->end()){
            continue;
        }

         // check if originalSelectNode is in nodeMap
        Assert((nodeMap->find(originalSeqNthNode) != nodeMap->end()));
        newSeqNthNode = (*nodeMap)[originalSeqNthNode];
        newSeqNode = newSeqNthNode[0];
        if (!newSeqNode.getType().isSequence()){
            newSeqNode = newSeqNode[0];
        }
        
        // check if originalArrayNode.getType() is not in ufArrays
        Assert(ufArrays->find(originalSeqNode.getType()) != ufArrays->end());

        arrToCons = (*ufArrays)[originalSeqNode.getType()][1];
        arrToConsApplication = nm->mkNode(Kind::APPLY_UF, arrToCons, newSeqNode);
        // insert the equality between the recursive element and the indexed element
        const DType& newDType = arrToConsApplication.getType().getDType();
        // iterate over the constructors    
        for (size_t i = 0, n = newDType.getNumConstructors(); i < n; ++i) {
            const DTypeConstructor& cons = newDType[i];
            if (cons.getNumArgs() == 0) {
                continue;
            }
            if (newSeqNode.getKind() == Kind::APPLY_UF){
                Node consToArrFunc = (*ufArrays)[originalSeqNode.getType()][0];
                // check if the function is consToArrFunc
                if (newSeqNode.getOperator() == consToArrFunc){      
                    arrToConsApplication = newSeqNode[0];
                }
            }
            Trace("nesteddtltag")  <<  "originalIndexNode: "  <<  originalIndexNode  <<  std::endl;
        
            std::vector<Node> oldIndexes = (*seqNthIndexes)[originalSeqNode.getType()];
            for (size_t j = 0; j < oldIndexes.size(); j++){
                if (oldIndexes[j] == originalIndexNode){
                    Trace("nesteddtltag")  <<  "oldIndexes[j]: "  <<  oldIndexes[j]  <<  std::endl;
                    selector = cons[j+1].getSelector();
                    selector_application = nm->mkNode(Kind::APPLY_SELECTOR, selector, arrToConsApplication);
                    if (newSeqNthNode.getType().isSequence() && !selector_application.getType().isSequence()){
                        // find current in ufArrays
                        Assert(ufArrays->find(originalSeqNthNode.getType()) != ufArrays->end()); 
                        Node consToNew = (*ufArrays)[originalSeqNthNode.getType()][0];
                        TypeNode t2 = consToNew.getType().getArgTypes()[0];
                        // check if t1 is equal to t2
                        assert (selector_application.getType() == t2);
                        selector_application = nm->mkNode(Kind::APPLY_UF, consToNew, selector_application);
                    }
                    assertion = nm->mkNode(Kind::EQUAL, selector_application, newSeqNthNode);
                    if (selector_application.hasOperator() && newSeqNthNode.hasOperator()){
                        if (selector_application.getOperator() == newSeqNthNode.getOperator()){
                            assertion = nm->mkNode(Kind::EQUAL, selector_application[0], newSeqNthNode[0]);
                        }
                    }
                    newAssertions->insert(assertion);
                    break;
                }
            }      
        } 
    } 
}

void Nesteddtl::addAssertionsSeqs(std::set<Node>* seqNthNodes, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::set<Node>* seqs, std::map<Node, Node>* nodeMap){
    Node first, assertion, notAssertion, newSeqNode, consToArrFunc, arrToConsFunc, applyArrToCons;
    TNode opNode;
        // iterate over the arrays
    for (const auto& originalSeq : (*seqs)) {
        Assert(nodeMap->find(originalSeq) != nodeMap->end());
        newSeqNode = (*nodeMap)[originalSeq];
        // check if the newArrayNode is a UF application
        if (newSeqNode.getKind() == Kind::APPLY_UF){
            consToArrFunc = (*ufArrays)[originalSeq.getType()][0];
            arrToConsFunc = (*ufArrays)[originalSeq.getType()][1];
            // check if the function is consToArrFunc
            if (newSeqNode.getOperator() == consToArrFunc){      
                // insert that application of array2cons is consistent   
                applyArrToCons = nm->mkNode(Kind::APPLY_UF, arrToConsFunc, newSeqNode);

                assertion = nm->mkNode(Kind::EQUAL, newSeqNode[0], applyArrToCons);
                newAssertions->insert(assertion);

                // insert it is not nil
                const DType& newDType = applyArrToCons.getType().getDType();
                size_t numConstructors = newDType.getNumConstructors();
                for (size_t i = 0; i < numConstructors; ++i) {
                    const DTypeConstructor& constructor = newDType[i];
                    if (constructor.getNumArgs() == 0) {
                        // create a TNode from the constructor
                        opNode = constructor.getConstructor();
                        first = nm->mkNode(Kind::APPLY_CONSTRUCTOR, opNode);
                        notAssertion = nm->mkNode(Kind::NOT, nm->mkNode(Kind::EQUAL, newSeqNode[0], first));
                        newAssertions->insert(notAssertion);
                        break;
                    }
                }
            }
        }
    }  
}

void Nesteddtl::addAssertionsStore(std::map<TypeNode, std::vector<Node>>* arrayIndexes, NodeManager* nm, std::set<Node>* newAssertions, std::map<TypeNode, std::vector<Node>>* ufArrays, std::set<Node>* storeNodes, std::map<Node, Node>* nodeMap){
    Node assertion, arrToConsFunc, newStoreNode, newArray, newIndex, newValue;
	Node array, index, value, newArrayCons, newStoreCons, oldIndex, selector, convertedOldIndex, applySelect, selector_store;
	TypeNode arrayType;
    //iterate over the storeNodes
    for (const auto& storeNode : (*storeNodes)) {
        //find the storeNode in the nodeMap
        Assert(nodeMap->find(storeNode) != nodeMap->end());
        newStoreNode = (*nodeMap)[storeNode];

        // get the newStoreNode's children
        newArray = newStoreNode[0];
        newIndex = newStoreNode[1];
        newValue = newStoreNode[2];

        // get the storeNode's children
        array = storeNode[0];
        index = storeNode[1];
        value = storeNode[2];
        // get the array's type
        arrayType = array.getType();
        // check if the arrayType is in ufArrays
        Assert(ufArrays->find(arrayType) != ufArrays->end());
        arrToConsFunc = (*ufArrays)[arrayType][1];

        // apply  the arrToConsFunc to the newArray
        newArrayCons = nm->mkNode(Kind::APPLY_UF, arrToConsFunc, newArray);
        newStoreCons = nm->mkNode(Kind::APPLY_UF, arrToConsFunc, newStoreNode);

        const DType& newDType = newArrayCons.getType().getDType();
        const DTypeConstructor& cons = newDType[0];
        // check if the arrayType is not in the arrayIndexes
        Assert(arrayIndexes->find(arrayType) != arrayIndexes->end());
        std::vector<Node> oldIndexes = (*arrayIndexes)[arrayType];
        // iterate over the oldIndexes
        for (size_t i = 0; i < oldIndexes.size(); i++){
            oldIndex = oldIndexes[i];
            selector = cons[i+1].getSelector();

            Assert(nodeMap->find(oldIndex) != nodeMap->end());
            convertedOldIndex = (*nodeMap)[oldIndex];
            applySelect = nm->mkNode(Kind::SELECT, newStoreNode, convertedOldIndex);
            selector_store = nm->mkNode(Kind::APPLY_SELECTOR, selector, newStoreCons);
            assertion = nm->mkNode(Kind::EQUAL, selector_store, applySelect);
            newAssertions->insert(assertion);

            applySelect = nm->mkNode(Kind::SELECT, newArray, convertedOldIndex);
            selector_store = nm->mkNode(Kind::APPLY_SELECTOR, selector, newArrayCons);
            assertion = nm->mkNode(Kind::EQUAL, selector_store, applySelect);
            newAssertions->insert(assertion);
        }
        
    }
}
}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
