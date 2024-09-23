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
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__NESTEDDTL_H */
