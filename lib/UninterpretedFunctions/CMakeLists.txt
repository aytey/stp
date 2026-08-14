add_library(uninterpretedfunctions OBJECT
    UFDecl.cpp
    UFContext.cpp
)

add_dependencies(uninterpretedfunctions ASTKind_header)

set_target_properties(uninterpretedfunctions PROPERTIES
    PUBLIC_HEADER
      "${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFDecl.h;${PROJECT_SOURCE_DIR}/include/stp/UninterpretedFunctions/UFContext.h"
)
