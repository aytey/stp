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

"""Several passes fill their memo from the bottom up before running, so that
their own recursion stops one level down and a deeply nested input does not
exhaust the stack (stp/Util/DagWalk.h). Doing that is only sound if the
priming visits exactly the nodes the pass would have visited anyway: prime a
node the pass would have skipped and it builds nodes that do not otherwise
exist, which shifts every node number after them and changes the CNF.

Nothing in the type system says a pass qualifies. This checks it instead, by
solving each query both ways -- priming on, which is how STP runs, and off,
which restores the recursion these passes used to do -- and requiring the
generated CNF to come out identical.

A difference means one of the passes that uses primeMemo no longer satisfies
its preconditions: most likely it grew a path that stops early without
looking at all of a node's children, or a classify() that no longer matches
which of them the pass reaches.
"""

import filecmp
import os
import shutil
import subprocess
import sys
import tempfile

TIMEOUT = 60


def cnf_for(stp, query, flag, workdir):
    """Solve `query` with priming on or off, returning the CNF files written.

    None if the run did not finish. That matters: the CNF is written as the
    solve goes, so a run cut short by the timeout leaves a partial file, and
    two partial runs of even the same binary differ from each other. Only
    completed runs can be compared.
    """
    out = os.path.join(workdir, flag)
    os.makedirs(out, exist_ok=True)

    try:
        done = subprocess.run(
            [stp, "--array-equality", "--prime-memos", flag, "--output-CNF",
             "--SMTLIB2", query],
            cwd=out, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return None

    if done.returncode != 0:
        return None
    return sorted(os.listdir(out))


def main():
    if len(sys.argv) != 3:
        print("usage: prime-memos-differential.py <stp binary> <query dir>")
        return 2

    stp, query_dir = sys.argv[1], sys.argv[2]
    if not os.path.isfile(stp) or not os.access(stp, os.X_OK):
        print("no stp binary at %s -- skipping" % stp)
        return 77 # ctest treats this as "skipped".

    queries = []
    for root, _, files in os.walk(query_dir):
        queries.extend(os.path.join(root, f) for f in sorted(files)
                       if f.endswith(".smt2"))
    queries.sort()

    if not queries:
        print("no queries under %s -- skipping" % query_dir)
        return 77

    compared = incomparable = 0
    differed = []

    for query in queries:
        workdir = tempfile.mkdtemp(prefix="prime-memos-")
        try:
            on = cnf_for(stp, query, "1", workdir)
            off = cnf_for(stp, query, "0", workdir)

            if on is None or off is None:
                incomparable += 1 # timed out, or the query is an error case.
                continue

            compared += 1
            match, mismatch, errors = filecmp.cmpfiles(
                os.path.join(workdir, "1"), os.path.join(workdir, "0"),
                on, shallow=False)
            if on != off or mismatch or errors:
                differed.append(os.path.basename(query))
        finally:
            shutil.rmtree(workdir, ignore_errors=True)

    print("compared %d queries (%d could not be compared)"
          % (compared, incomparable))

    if differed:
        print("the CNF differs with priming on and off, for:")
        for name in differed[:20]:
            print("    " + name)
        print("A pass that primes its memo no longer visits the same nodes "
              "the recursion did. See stp/Util/DagWalk.h.")
        return 1

    if compared == 0:
        print("nothing could be compared -- skipping")
        return 77

    return 0


if __name__ == "__main__":
    sys.exit(main())
