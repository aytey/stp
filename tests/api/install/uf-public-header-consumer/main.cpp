#include "stp/fp.hpp"
#include "stp/uf.hpp"

int main()
{
  VC checker = vc_createValidityChecker();
  if (checker == nullptr)
    return 1;

  stp::uf::Context context(checker);
  stp::uf::Function function = context.declareUninterpretedFunction(
      "installed_cpp_f", {stp::uf::Sort::bitVector(8)},
      stp::uf::Sort::bitVector(8));
  Expr argument = vc_bvConstExprFromInt(checker, 8, 42);
  Expr application = function({argument});
  const bool correctKind = getExprKind(application) == UF_APPLY;

  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(checker);
  return correctKind ? 0 : 2;
}
