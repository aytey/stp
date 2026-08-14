#include "stp/c_interface.h"

int main(void)
{
  VC checker = vc_createValidityChecker();
  if (checker == 0)
    return 1;

  vc_setFlag(checker, 'u');
  Type bv8 = vc_bvType(checker, 8);
  UFDeclHandle function = vc_declareUninterpretedFunction(
      checker, "installed_c_f", &bv8, 1, bv8);
  vc_DeleteExpr(bv8);
  if (function == 0)
  {
    vc_Destroy(checker);
    return 2;
  }

  Expr argument = vc_bvConstExprFromInt(checker, 8, 42);
  Expr arguments[] = {argument};
  Expr application =
      vc_applyUninterpretedFunction(checker, function, arguments, 1);
  if (application == 0 || getExprKind(application) != UF_APPLY)
  {
    vc_DeleteExpr(application);
    vc_DeleteExpr(argument);
    vc_Destroy(checker);
    return 3;
  }

  vc_DeleteExpr(application);
  vc_DeleteExpr(argument);
  vc_Destroy(checker);
  return 0;
}
