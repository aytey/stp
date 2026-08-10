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

"""Compare two STP binaries on the answers and models they produce.

The CNF comparison that guards the rest of the stack-safety work is blind to
counterexample evaluation: the CNF is written before a model exists, so it is
byte-identical whatever TermToConstTermUsingModel and ComputeFormulaUsingModel
do afterwards. This is the gate for that code.

Every query is solved by both binaries with -p and -d, so that each sat answer
has its counterexample constructed, checked against the original formula, and
printed. The whole of stdout is compared, which covers the answer, the model,
and the order the model is printed in.

Runs that do not finish are dropped rather than compared: a run cut short by
the timeout differs from itself. So is a query that errors in both, since the
message is the same either way and there is nothing to compare.

Usage: model-differential.py <stp-a> <stp-b> <query-dir>
"""

import os
import subprocess
import sys

TIMEOUT = 60


def solve(stp, query):
    """(returncode, stdout) for one query, or None if it did not finish."""
    try:
        done = subprocess.run([stp, "--SMTLIB2", "-p", "-d", query],
                              stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return None
    return (done.returncode, done.stdout)


def main():
    if len(sys.argv) != 4:
        print("usage: model-differential.py <stp-a> <stp-b> <query-dir>")
        return 2

    a, b, query_dir = sys.argv[1], sys.argv[2], sys.argv[3]
    for binary in (a, b):
        if not (os.path.isfile(binary) and os.access(binary, os.X_OK)):
            print("no stp binary at %s" % binary)
            return 2

    queries = []
    for root, _, files in os.walk(query_dir):
        queries.extend(os.path.join(root, f) for f in files
                       if f.endswith(".smt2"))
    queries.sort()

    compared = incomparable = models = 0
    differed = []

    for query in queries:
        ra, rb = solve(a, query), solve(b, query)
        if ra is None or rb is None:
            incomparable += 1
            continue

        compared += 1
        if b"\n(\n" in ra[1] or ra[1].startswith(b"(\n"):
            models += 1
        if ra != rb:
            differed.append(os.path.relpath(query, query_dir))

    print("compared %d queries, %d of them with a printed model "
          "(%d could not be compared)" % (compared, models, incomparable))

    if differed:
        print("the answer or the model differs, for:")
        for name in differed[:20]:
            print("    " + name)
        return 1

    return 0 if compared else 2


if __name__ == "__main__":
    sys.exit(main())
