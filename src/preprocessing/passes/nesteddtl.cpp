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
    : PreprocessingPass(preprocContext, "Nesteddtl") {
}

PreprocessingPassResult Nesteddtl::applyInternal(
    AssertionPipeline* assertionsToPreprocess) {
    // Get the NodeManager
    NodeManager* nm = NodeManager::currentNM();

    Trace("nesteddtltag")  <<  "Inside pp"   <<  std::endl;

    // Get the MyDataStorage instance
    //theory::nesteddt::MyDataStorage& dataStorage =
    //  theory::nesteddt::MyDataStorage::getInstance();

    // Get the assertion
    //dataStorage.check = 1;

    return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
