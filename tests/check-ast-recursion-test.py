#!/usr/bin/env python3
# AUTHORS: Andrew Teylu

import importlib.util
import pathlib
import sys
import tempfile
import unittest


def load_checker(path):
    spec = importlib.util.spec_from_file_location("ast_recursion_audit", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CHECKER = load_checker(sys.argv[1])


class ASTRecursionAuditTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def write(self, relative, source):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        return path.parent

    def scan(self, *roots):
        return CHECKER.recursive_ast_walkers([str(root) for root in roots])

    def test_finds_direct_recursion_for_ast_node_and_ast_container(self):
        self.write("walkers.cpp", r"""
ASTNode
direct(const ASTNode& node)
{
  return direct(node[0]);
}

ASTVec flatten(const ASTChildren& nodes)
{
  return flatten(nodes);
}
""")

        self.assertEqual({"direct", "flatten"}, set(self.scan(self.root)))

    def test_finds_mutual_recursion_across_source_roots(self):
        first = self.write("first/left.cpp", r"""
ASTNode right(const ASTNode& node);
ASTNode left(const ASTNode& node)
{
  return right(node[0]);
}
""")
        second = self.write("second/right.cpp", r"""
ASTNode left(const ASTNode& node);
ASTNode right(const ASTNode& node)
{
  return left(node[0]);
}
""")

        self.assertEqual({"left <-> right"}, set(self.scan(first, second)))

    def test_finds_mutual_recursion_in_ast_derived_graph(self):
        self.write("mirror.h", r"""
class Mirror
{
  ASTNode source;
  std::vector<Mirror*> children;

  void descendLeft()
  {
    children[0]->descendRight();
  }

  void descendRight()
  {
    children[0]->descendLeft();
  }
};
""")

        self.assertEqual(
            {"Mirror::descendLeft <-> Mirror::descendRight"},
            set(self.scan(self.root)))

    def test_ignores_mutual_recursion_that_carries_no_ast_graph(self):
        self.write("integers.cpp", r"""
int right(int value);
int left(int value)
{
  return right(value - 1);
}

int right(int value)
{
  return left(value - 1);
}
""")

        self.assertEqual({}, self.scan(self.root))

    def test_does_not_parse_calls_or_control_flow_as_definitions(self):
        self.write("calls.cpp", r"""
ASTNode passthrough(const ASTNode& node)
{
  if (predicate(node))
  {
    visitor.visit(node);
  }
  return node;
}

std::function<ASTNode(const ASTNode&)> lambda =
    [&](const ASTNode& node) { return passthrough(node); };
""")

        self.assertEqual({}, self.scan(self.root))
        sources = CHECKER.read_sources([str(self.root)])
        self.assertNotIn("ASTNode", CHECKER.parse_functions(sources))

    def test_finds_named_recursive_std_function_lambda(self):
        self.write("lambda.cpp", r"""
void owner(const ASTNode& root)
{
  std::function<void(const ASTNode&)> descend =
      [&](const ASTNode& node) { descend(node[0]); };
  descend(root);
}
""")

        self.assertEqual({"<lambda descend>"}, set(self.scan(self.root)))

    def test_scc_analysis_does_not_recurse_on_the_python_stack(self):
        size = 5000
        edges = {str(i): {str(i + 1)} for i in range(size - 1)}
        edges[str(size - 1)] = {"0"}

        components = CHECKER.strongly_connected_components(edges)

        self.assertEqual(1, len(components))
        self.assertEqual(size, len(components[0]))


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0]])
