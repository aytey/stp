#include "stp/UninterpretedFunctions/UFChecker.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include "stp/UninterpretedFunctions/UFLemma.h"
#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"

int main()
{
  stp::UFConcreteValue value = stp::UFConcreteValue::fromUInt(8, 42);
  return value.bytes().empty() ? 1 : 0;
}
