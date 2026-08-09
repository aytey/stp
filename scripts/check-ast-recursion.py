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

"""Find functions that walk the AST by calling themselves.

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

The parsing is deliberately crude: no compiler, just brace matching over the
source with comments and strings removed. It over-reports -- a forwarding
overload looks the same as a recursive walk from here -- which is why the
allowlist carries a reason for each entry rather than just a name. It is a
tripwire for review, not a proof.
"""

import os
import re
import sys

SKIP_DIRS = {"extlib-abc", "extlib-mimalloc", "extlib-symfpu", "extlib-cli11",
             "extlib-constbv", "extlib-unordered-dense", "extlib-riss",
             "extlib-minisat", "extlib-cryptominisat"}

# A definition line: everything before the parameter list is type and name
# characters, which a statement -- with its `=` or `;` or `->` -- is not. The
# function is the last qualified name on it, since a return type can itself
# be qualified (NodeDomainAnalysis::DomainInfo NodeDomainAnalysis::buildMap).
DEFINITION_LINE = re.compile(r'^[ \t]*[\w:<>,&*~\s]*\(')
QUALIFIED = re.compile(r'(\w+)::(\w+)\s*\(')
# Free functions too -- the printers are ordinary functions in a namespace,
# and a recursive one there crashes just the same.
PLAIN = re.compile(r'(\w+)\s*\($')


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


def body_after(src, start):
    """The braced body beginning at or after `start`, or None."""
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
                return src[open_brace:i]
    return None


def self_recursive_ast_walkers(root):
    found = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for name in sorted(filenames):
            if not name.endswith((".cpp", ".h")):
                continue
            path = os.path.join(dirpath, name)
            with open(path, errors="ignore") as handle:
                src = strip_comments_and_strings(handle.read())

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
                        continue # a constructor.
                    end = last.end()
                else:
                    plain = PLAIN.search(line[:line.index("(") + 1])
                    if plain is None:
                        continue
                    cls, func = "", plain.group(1)
                    if func in ("if", "for", "while", "switch", "return",
                                "sizeof", "assert"):
                        continue
                    end = plain.end()

                body = body_after(src, start + end)
                if body is None:
                    continue

                # Takes or returns a node. Mentioning one somewhere in a
                # long body is not the same thing -- what matters is a
                # function whose argument is the node it walks.
                signature = line[:line.index("(")] + \
                    src[start + line.index("("):src.find("{", start + end)]
                if "ASTNode" not in signature:
                    continue

                if re.search(r'(?<![\w:.>])' + re.escape(func) + r'\s*\(', body):
                    label = ("%s::%s" % (cls, func)) if cls else func
                    found.setdefault(label, os.path.relpath(path, root))
    return found


def read_allowlist(path):
    allowed = {}
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            # Split on colon-space: the names themselves contain "::".
            name, _, reason = line.partition(": ")
            allowed[name.strip()] = reason.strip()
    return allowed


def main():
    if len(sys.argv) < 3:
        print("usage: check-ast-recursion.py <allowlist> <source root>...")
        return 2

    allowlist_path, roots = sys.argv[1], sys.argv[2:]
    found = {}
    for root in roots:
        found.update(self_recursive_ast_walkers(root))
    allowed = read_allowlist(allowlist_path)

    added = sorted(set(found) - set(allowed))
    gone = sorted(set(allowed) - set(found))
    unexplained = sorted(n for n in set(found) & set(allowed) if not allowed[n])

    if added:
        print("These walk the AST by calling themselves and are not in %s:\n"
              % os.path.basename(allowlist_path))
        for name in added:
            print("    %-52s %s" % (name, found[name]))
        print("\nA pass that calls itself once per level of the input runs out"
              "\nof stack on input deep enough -- which is a crash on a valid"
              "\nquery, and how ten of these were found. Either walk it with"
              "\nits frames on the heap (stp/Util/DagWalk.h has the two ways"
              "\nthat have been used, and DeepDag_Test.cpp has the tests), or"
              "\nadd it to the allowlist with the reason it is safe.")
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

    print("%d self-recursive AST walkers, all accounted for" % len(found))
    return 0


if __name__ == "__main__":
    sys.exit(main())
