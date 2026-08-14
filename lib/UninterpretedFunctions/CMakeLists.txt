add_library(uninterpretedfunctions OBJECT
    UFDecl.cpp
    UFContext.cpp
    UFLowering.cpp
    UFChecker.cpp
    UFLemma.cpp
    UFRefinement.cpp
    UFModel.cpp
)

add_dependencies(uninterpretedfunctions ASTKind_header)

set_target_properties(uninterpretedfunctions PROPERTIES
    PUBLIC_HEADER
      "${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFDecl.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFContext.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFLowering.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFChecker.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFLemma.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFRefinement.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFModel.h"
)
