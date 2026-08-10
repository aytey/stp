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
overload looks the same as a recursive walk from here -- which is why each
allowlist line carries a status and a reason rather than just a name. It is a
tripwire for review, not a proof.

It under-reports too, in two ways worth knowing about.

It only sees a function that calls *itself*. Two functions that call each
other once per level are just as unbounded and are invisible here:
TermToConstTermUsingModel recurses through its own _inner overload and does
not appear below, though it is where a deep array read now lands.

And a function only counts if an ASTNode appears in its signature, which
keeps the output down to something reviewable but misses a walk over a
structure *built* from the input: VariablesInExpression's Symbols tree and RemoveUnconstrained's
MutableASTNode graph are both as deep as the formula they came from, and
neither mentions an ASTNode on the way down. Both were found by running a
pass at depth, not by reading it, and MutableASTNode::propagateUpDirty still
walks up the parents that way. Anything that mirrors the input's shape wants
the same treatment whether or not this script can see it.
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
# A definition written inside its class body carries no Class:: prefix, so the
# class is recovered from the braces around it. Without this, MutableASTNode's
# walk is listed as plain "build", which says nothing about where it is and
# would silently merge with any other in-class build() taking a node.
CLASS_DECL = re.compile(r'(?<!enum )\b(?:class|struct)\s+(?:DLL_PUBLIC\s+)?'
                        r'(\w+)\b[^;{]*\{')

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
            spans = class_extents(src)

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
                    # Written inside its class body, or a free function.
                    cls, func = enclosing_class(spans, start), plain.group(1)
                    if cls == func:
                        continue # a constructor.
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
    found = {}
    for root in roots:
        found.update(self_recursive_ast_walkers(root))
    allowed = read_allowlist(allowlist_path)

    added = sorted(set(found) - set(allowed))
    gone = sorted(set(allowed) - set(found))
    both = set(found) & set(allowed)
    unexplained = sorted(n for n in both if not allowed[n][1])
    mislabelled = sorted(n for n in both if allowed[n][0] not in STATUSES)

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
    print("%d self-recursive AST walkers, all accounted for: %s"
          % (len(found), ", ".join("%d %s" % (tally[s], s)
                                   for s in sorted(tally))))
    return 0


if __name__ == "__main__":
    sys.exit(main())
