#include "stp/c_interface.h"

int main(void)
{
  VC checker = vc_createValidityChecker();
  if (checker == 0)
    return 1;
  vc_Destroy(checker);
  return 0;
}
