#!/usr/bin/env python3
# AUTHORS: Andrew Teylu
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

"""Find recursive call cycles that can walk an AST-shaped graph.

How deeply a formula nests is the input's choice, so a pass that calls itself
once per level runs out of stack on input that is deep enough. STP had ten
such passes and every one of them crashed on inputs from a benchmark
campaign; they are now walked with their frames on the heap (see
stp/Util/DagWalk.h and tests/unit-tests/DeepDag_Test.cpp).

Nothing stops the next one being written -- recursing over a DAG is the
natural way to express these passes, and the crash only shows up on input
nobody has yet. So this lists them, and requires each to be written down in
the allowlist beside it with a reason. Adding a recursive walk is allowed;
adding one silently is not.

The parsing is deliberately lightweight: no compiler, just brace matching
over source with comments and strings removed. Calls are resolved exactly
when qualified, within the owning class when unqualified, and by unique name
otherwise. Strongly connected components of that call graph expose both
direct recursion and functions that recurse through one another.

An AST-shaped graph is either an AST container named below, or a self-linked
class that contains one. The latter is how the audit covers structures built
from an input AST, such as Symbols and MutableASTNode, even when a walk over
them no longer mentions ASTNode in its own signature.

This remains a review tripwire, not a proof: overload forwarding and bounded
recursion look like walks and are deliberately reported. That is why every
allowlist entry carries a status and a reason rather than merely a name.

Named std::function lambdas are checked separately. They do not have a C++
function definition for the ordinary call graph to name, but a lambda which
calls the variable holding itself is the same input-depth recursion -- with
an additional indirect call at every level -- and must not sit outside the
audit merely because its body is local to another function.
"""

import os
import re
import sys

SKIP_DIRS = {"extlib-abc", "extlib-mimalloc", "extlib-symfpu", "extlib-cli11",
             "extlib-constbv", "extlib-unordered-dense", "extlib-riss",
             "extlib-minisat", "extlib-cryptominisat"}

# A possible definition line. The checks in parse_functions reject control
# flow, calls, template arguments, constructors and declarations after this
# deliberately broad first pass.
DEFINITION_LINE = re.compile(r'^[ \t]*[\w:<>,&*~\s]*\(')
QUALIFIED = re.compile(r'(\w+)::(\w+)\s*\(')
# Free functions too -- the printers are ordinary functions in a namespace,
# and a recursive one there crashes just the same.
PLAIN = re.compile(r'(\w+)\s*\($')
CALL = re.compile(r'(?:(\w+)::)?(\w+)\s*\(')
# A definition written inside its class body carries no Class:: prefix, so the
# class is recovered from the braces around it. Without this, MutableASTNode's
# walk is listed as plain "build", which says nothing about where it is and
# would silently merge with any other in-class build() taking a node.
CLASS_DECL = re.compile(r'(?<!enum )\b(?:class|struct)\s+(?:DLL_PUBLIC\s+)?'
                        r'(\w+)\b(?!\s*[>,])[^;{]*\{')

# Types that directly carry nodes or node collections. Self-linked classes
# containing one of these are added transitively by ast_graph_types().
AST_TYPES = {"ASTNode", "ASTVec", "ASTChildren", "ASTNodeMap", "ASTNodeSet"}

CONTROL_WORDS = {"if", "for", "while", "switch", "return", "sizeof",
                 "assert", "static_cast", "dynamic_cast",
                 "reinterpret_cast", "const_cast", "decltype"}

# What an allowlist line claims. Anything else is rejected, so a new entry
# has to say which of these it is rather than describing itself freely.
STATUSES = {
    "safe":      "not a walk over the input: an overload forwarding to one, "
                 "or bounded by something that is not input depth",
    "bounded":   "recurses, but its memo is filled from the bottom first, so "
                 "it stops one level down",
    "partial":   "the recursion is gone on the paths that have been measured, "
                 "and the shape that still reaches it is named on the line",
    "by-choice": "input-depth recursive on purpose, with a case in "
                 "DeepDag_Test.cpp saying so",
    "off-path":  "input-depth recursive, but nothing a solve does reaches it "
                 "-- the line says what does",
    "on-path":   "input-depth recursive on a path a solve takes, and not "
                 "converted; the line says the depth it was measured to die at",
    "unaudited": "predates this check and has not been looked at",
}


def strip_comments_and_strings(src):
    """Remove comments and string literals, keeping newlines so lines align.

    Without this a comment that merely mentions a function's name reads as a
    call to it -- which is exactly what happens where a converted pass
    explains what its recursive version used to do.
    """
    out = []
    i = 0
    n = len(src)
    while i < n:
        two = src[i:i + 2]
        if two == "//":
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif two == "/*":
            j = src.find("*/", i + 2)
            end = n if j < 0 else j + 2
            out.append("\n" * src.count("\n", i, end))
            i = end
        elif src[i] in "\"'":
            quote = src[i]
            j = i + 1
            while j < n and src[j] != quote:
                j += 2 if src[j] == "\\" else 1
            i = min(j + 1, n)
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def body_extent_after(src, start):
    """(open brace, close brace) for the body after `start`, or None."""
    open_brace = src.find("{", start)
    if open_brace < 0:
        return None
    # A declaration ends before any body begins.
    semicolon = src.find(";", start)
    if 0 <= semicolon < open_brace:
        return None

    depth = 0
    for i in range(open_brace, len(src)):
        if src[i] == "{":
            depth += 1
        elif src[i] == "}":
            depth -= 1
            if depth == 0:
                return open_brace, i
    return None


def body_after(src, start):
    """The braced body beginning at or after `start`, or None."""
    extent = body_extent_after(src, start)
    return None if extent is None else src[extent[0]:extent[1]]


def class_extents(src):
    """(open, close, name) for every class/struct body in `src`."""
    spans = []
    for m in CLASS_DECL.finditer(src):
        open_brace = m.end() - 1
        depth = 0
        for i in range(open_brace, len(src)):
            if src[i] == "{":
                depth += 1
            elif src[i] == "}":
                depth -= 1
                if depth == 0:
                    spans.append((open_brace, i, m.group(1)))
                    break
    return spans


def enclosing_class(spans, pos):
    """The innermost class whose body contains `pos`, or ""."""
    best = None
    for open_brace, close_brace, name in spans:
        if open_brace < pos < close_brace:
            if best is None or open_brace > best[0]:
                best = (open_brace, name)
    return best[1] if best else ""


def read_sources(roots):
    """Read source once, retaining the root used for display paths."""
    sources = []
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            for name in sorted(filenames):
                if not name.endswith((".cpp", ".h")):
                    continue
                path = os.path.join(dirpath, name)
                with open(path, errors="ignore") as handle:
                    src = strip_comments_and_strings(handle.read())
                sources.append((root, path, src, class_extents(src)))
    return sources


def ast_graph_types(sources):
    """Names of AST containers and self-linked mirrors of those containers."""
    graph_types = set(AST_TYPES)
    classes = []

    def member_declarations(body):
        """Semicolon-terminated text at the outer class body's own level."""
        at_level = []
        depth = 0
        for char in body:
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
            elif depth == 1:
                at_level.append(char)
        return [d for d in "".join(at_level).split(";") if "(" not in d]

    for _, _, src, spans in sources:
        for open_brace, close_brace, name in spans:
            classes.append((name, member_declarations(
                src[open_brace:close_brace])))

    # A graph node points to another node of its own type and carries an AST
    # node (or another graph type). Iterate so wrappers around a mirror are
    # recognised too.
    changed = True
    while changed:
        changed = False
        for name, declarations in classes:
            if name in graph_types:
                continue
            self_linked = any(
                re.search(r'\b' + re.escape(name) + r'\s*\*', declaration)
                for declaration in declarations)
            carries_graph = any(
                re.search(r'\b' + re.escape(t) + r'\b', declaration)
                for declaration in declarations for t in graph_types)
            if self_linked and carries_graph:
                graph_types.add(name)
                changed = True
    return graph_types


def parse_functions(sources):
    """label -> definitions collapsed across overloads."""
    def looks_like_return_type(text):
        text = text.strip()
        if not text or not re.match(r'^[\w:<>,&*~\s]+$', text):
            return False
        return not any(re.search(r'\b' + word + r'\b', text)
                       for word in CONTROL_WORDS)

    functions = {}
    for root, path, src, spans in sources:
        offset = 0
        for line in src.split("\n"):
            start = offset
            offset += len(line) + 1

            if not DEFINITION_LINE.match(line):
                continue
            names = list(QUALIFIED.finditer(line))
            if names:
                last = names[-1]
                cls, func = last.group(1), last.group(2)
                if cls == func:
                    continue  # a constructor.
                end = last.end()
            else:
                plain = PLAIN.search(line[:line.index("(") + 1])
                if plain is None:
                    continue
                cls, func = enclosing_class(spans, start), plain.group(1)
                if cls == func or func in CONTROL_WORDS:
                    continue
                prefix = line[:plain.start()]
                # The name of a function follows whitespace, `*`, or `&`.
                # In `std::function<ASTNode(...)>` ASTNode is a template
                # argument, not the name of a lambda or function definition.
                if (prefix and not prefix[-1].isspace() and
                        prefix[-1] not in "*&"):
                    continue
                if not looks_like_return_type(prefix):
                    # A few definitions put the return type on the preceding
                    # line. A bare `foo(` everywhere else is a call, not a
                    # definition whose body happens to be the next block.
                    previous_end = max(0, start - 1)
                    previous_start = src.rfind("\n", 0, previous_end)
                    previous = src[previous_start + 1:previous_end]
                    if not looks_like_return_type(previous):
                        continue
                end = plain.end()

            extent = body_extent_after(src, start + end)
            if extent is None:
                continue
            open_brace, close_brace = extent
            label = ("%s::%s" % (cls, func)) if cls else func
            entry = functions.setdefault(
                label, {"class": cls, "name": func, "signatures": [],
                        "bodies": [], "path": os.path.relpath(path, root)})
            entry["signatures"].append(src[start:open_brace])
            entry["bodies"].append(src[open_brace:close_brace])
    return functions


def recursive_graph_lambdas(sources, graph_types):
    """Named std::function lambdas which call themselves on an AST type."""
    graph_pattern = re.compile(
        r'\b(?:' + "|".join(re.escape(t) for t in sorted(graph_types)) + r')\b')
    found = {}

    for root, path, src, _ in sources:
        at = 0
        marker = "std::function"
        while True:
            begin = src.find(marker, at)
            if begin < 0:
                break
            at = begin + len(marker)

            angle = src.find("<", at)
            if angle < 0:
                continue
            depth = 0
            close = -1
            for i in range(angle, len(src)):
                if src[i] == "<":
                    depth += 1
                elif src[i] == ">":
                    depth -= 1
                    if depth == 0:
                        close = i
                        break
            if close < 0:
                continue

            signature = src[angle + 1:close]
            if not graph_pattern.search(signature):
                at = close + 1
                continue

            declaration = re.match(r'\s*([A-Za-z_]\w*)\s*=\s*',
                                   src[close + 1:])
            if declaration is None:
                at = close + 1
                continue
            name = declaration.group(1)
            initializer = close + 1 + declaration.end()
            extent = body_extent_after(src, initializer)
            if extent is None:
                at = initializer
                continue
            body = src[extent[0]:extent[1]]
            if re.search(r'\b' + re.escape(name) + r'\s*\(', body):
                found["<lambda %s>" % name] = os.path.relpath(path, root)
            at = extent[1] + 1

    return found


def graph_parameter_names(signatures, graph_types):
    """Names of parameters whose declared type is AST-shaped."""
    type_pattern = re.compile(
        r'\b(?:' + "|".join(re.escape(t) for t in sorted(graph_types)) + r')\b')
    names = set()
    for signature in signatures:
        left = signature.find("(")
        right = signature.rfind(")")
        if left < 0 or right < left:
            continue
        parameters = signature[left + 1:right]

        # Commas inside templates do not separate parameters.
        pieces = []
        begin = depth = 0
        for i, char in enumerate(parameters):
            if char in "<([":
                depth += 1
            elif char in ">)]":
                depth = max(0, depth - 1)
            elif char == "," and depth == 0:
                pieces.append(parameters[begin:i])
                begin = i + 1
        pieces.append(parameters[begin:])

        for parameter in pieces:
            parameter = parameter.split("=", 1)[0]
            if not type_pattern.search(parameter):
                continue
            identifiers = re.findall(r'\b[A-Za-z_]\w*\b', parameter)
            if identifiers and identifiers[-1] not in graph_types:
                names.add(identifiers[-1])
    return names


def call_arguments(body, open_paren):
    """Text within the call parenthesis at open_paren."""
    depth = 0
    for i in range(open_paren, len(body)):
        if body[i] == "(":
            depth += 1
        elif body[i] == ")":
            depth -= 1
            if depth == 0:
                return body[open_paren + 1:i]
    return ""


def call_graph(functions, graph_types):
    """Return all call edges and those visibly carrying a graph argument."""
    by_name = {}
    for label, function in functions.items():
        by_name.setdefault(function["name"], set()).add(label)
        function["graph_params"] = graph_parameter_names(
            function["signatures"], graph_types)

    edges = {label: set() for label in functions}
    graph_edges = {label: set() for label in functions}
    for label, function in functions.items():
        for body in function["bodies"]:
            for call in CALL.finditer(body):
                scope, name = call.groups()
                if name in CONTROL_WORDS:
                    continue

                before = body[:call.start()].rstrip()
                receiver_call = before.endswith(".") or before.endswith(">")

                target = None
                if scope:
                    qualified = "%s::%s" % (scope, name)
                    if qualified in functions:
                        target = qualified
                else:
                    same_class = (("%s::%s" % (function["class"], name))
                                  if function["class"] else name)
                    derived_owner = (function["class"] in graph_types and
                                     function["class"] not in AST_TYPES)
                    explicit_this = bool(re.search(r'\bthis\s*->\s*$', before))
                    if (same_class in functions and
                            (not receiver_call or explicit_this or
                             derived_owner)):
                        target = same_class
                    elif not receiver_call and name in functions:
                        # A free function.
                        target = name
                    elif (not receiver_call and
                          len(by_name.get(name, ())) == 1):
                        target = next(iter(by_name[name]))

                if target is not None:
                    edges[label].add(target)
                    arguments = call_arguments(body, call.end() - 1)
                    carries_parameter = any(
                        re.search(r'\b' + re.escape(p) + r'\b', arguments)
                        for p in function["graph_params"])

                    # A graph-node method walking to another node of its own
                    # class often carries the graph in the receiver, with no
                    # explicit argument (child->walk()).
                    derived_owner = (function["class"] in graph_types and
                                     function["class"] not in AST_TYPES)
                    same_owner = (functions[target]["class"] ==
                                  function["class"])
                    prefix = body[max(0, call.start() - 160):call.start()]
                    receiver_carries = any(
                        re.search(r'\b' + re.escape(p) +
                                  r'\b[^;{}\n]*?(?:->|\.)\s*$', prefix)
                        for p in function["graph_params"])
                    if (carries_parameter or receiver_carries or
                            (derived_owner and same_owner)):
                        graph_edges[label].add(target)
    return edges, graph_edges


def strongly_connected_components(edges):
    """Kosaraju's algorithm with explicit DFS stacks."""
    visited = set()
    finish_order = []

    for root in edges:
        if root in visited:
            continue
        visited.add(root)
        stack = [(root, iter(edges[root]))]
        while stack:
            node, children = stack[-1]
            try:
                child = next(children)
            except StopIteration:
                finish_order.append(node)
                stack.pop()
                continue
            if child not in visited:
                visited.add(child)
                stack.append((child, iter(edges[child])))

    reverse_edges = {node: set() for node in edges}
    for parent, children in edges.items():
        for child in children:
            reverse_edges[child].add(parent)

    assigned = set()
    result = []
    for root in reversed(finish_order):
        if root in assigned:
            continue
        assigned.add(root)
        component = []
        stack = [root]
        while stack:
            node = stack.pop()
            component.append(node)
            for parent in reverse_edges[node]:
                if parent not in assigned:
                    assigned.add(parent)
                    stack.append(parent)
        result.append(component)
    return result


def recursive_ast_walkers(roots):
    sources = read_sources(roots)
    graph_types = ast_graph_types(sources)
    functions = parse_functions(sources)
    edges, graph_edges = call_graph(functions, graph_types)

    graph_pattern = re.compile(
        r'\b(?:' + "|".join(re.escape(t) for t in sorted(graph_types)) + r')\b')
    graph_functions = set()
    for label, function in functions.items():
        derived_owner = (function["class"] in graph_types and
                         function["class"] not in AST_TYPES)
        signatures = function["signatures"]
        if function["class"]:
            qualified = function["class"] + "::" + function["name"]
            signatures = [s.replace(qualified, function["name"])
                          for s in signatures]
        if derived_owner or any(graph_pattern.search(s) for s in signatures):
            graph_functions.add(label)

    found = {}
    found.update(recursive_graph_lambdas(sources, graph_types))
    # Preserve the original audit's direct-recursion coverage. It is
    # intentionally syntactic and therefore also catches overload forwarding.
    for label in graph_functions:
        if label in edges[label]:
            found[label] = functions[label]["path"]

    # A graph-carrying SCC is one indirect/mutual recursion finding. Keep the
    # whole cycle on one allowlist line; its members need one joint argument,
    # not a copy of that argument beside every helper.
    for component in strongly_connected_components(graph_edges):
        if len(component) < 2:
            continue
        label = " <-> ".join(sorted(component))
        paths = sorted(set(functions[n]["path"] for n in component))
        found[label] = paths[0] + ((" (+%d files)" % (len(paths) - 1))
                                  if len(paths) > 1 else "")

    return found


def self_recursive_ast_walkers(root):
    """Compatibility wrapper for callers of the original one-root API."""
    return recursive_ast_walkers([root])


def read_allowlist(path):
    """name -> (status, reason). Malformed lines get an empty status, which
    main() rejects rather than passing over."""
    allowed = {}
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            # Split on colon-space: the names themselves contain "::".
            name, _, rest = line.partition(": ")
            status, sep, reason = rest.partition(": ")
            if not sep:
                # `name: status` with nothing after it: a status and an
                # empty reason, which reads better than a status of "safe:".
                status, reason = rest.rstrip(":").strip(), ""
            allowed[name.strip()] = (status.strip(), reason.strip())
    return allowed


def main():
    if len(sys.argv) < 3:
        print("usage: check-ast-recursion.py <allowlist> <source root>...")
        return 2

    allowlist_path, roots = sys.argv[1], sys.argv[2:]
    found = recursive_ast_walkers(roots)
    allowed = read_allowlist(allowlist_path)

    added = sorted(set(found) - set(allowed))
    gone = sorted(set(allowed) - set(found))
    both = set(found) & set(allowed)
    unexplained = sorted(n for n in both if not allowed[n][1])
    mislabelled = sorted(n for n in both if allowed[n][0] not in STATUSES)

    if added:
        print("These recursively walk an AST-shaped graph and are not in %s:\n"
              % os.path.basename(allowlist_path))
        for name in added:
            print("    %-52s %s" % (name, found[name]))
        print("\nA recursive call cycle taken once per input level runs out"
              "\nof stack on input deep enough -- which is a crash on a valid"
              "\nquery, and how ten of these were found. Either walk it with"
              "\nits frames on the heap (stp/Util/DagWalk.h has the two ways"
              "\nthat have been used, and DeepDag_Test.cpp has the tests), or"
              "\nadd it to the allowlist as `name: status: reason`.")
        return 1

    if mislabelled:
        print("These carry no status, or one that is not a status:")
        for name in mislabelled:
            print("    %-52s %s" % (name, allowed[name][0] or "(empty)"))
        print("\nEvery line reads `name: status: reason`. The statuses are:")
        for status in sorted(STATUSES):
            print("    %-11s %s" % (status, STATUSES[status]))
        return 1

    if unexplained:
        print("Allowlisted without a reason: %s" % ", ".join(unexplained))
        return 1

    if gone:
        print("In %s but no longer found -- please delete these lines:"
              % os.path.basename(allowlist_path))
        for name in gone:
            print("    " + name)
        return 1

    tally = {}
    for name in found:
        tally[allowed[name][0]] = tally.get(allowed[name][0], 0) + 1
    print("%d recursive AST-shaped walkers, all accounted for: %s"
          % (len(found), ", ".join("%d %s" % (tally[s], s)
                                   for s in sorted(tally))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
