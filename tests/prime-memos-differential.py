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
observable result and generated CNF to come out identical.

A difference means one of the passes that uses primeMemo no longer satisfies
its preconditions: most likely it grew a path that stops early without
looking at all of a node's children, or a classify() that no longer matches
which of them the pass reaches. A crash, timeout, or other non-zero exit is a
difference too. Negative tests and tests whose declared feature requirements
are not present are excluded before running; every selected query must finish
on both sides, so a newly incomparable pair cannot silently shrink coverage.
"""

import filecmp
import os
import re
import shutil
import subprocess
import sys
import tempfile

try:
    import resource
except ImportError:  # Windows has no POSIX stack resource limit.
    resource = None

TIMEOUT = 60
CHILD_STACK_BYTES = 256 * 1024 * 1024


def raise_child_stack_limit():
    """Give the deliberately recursive baseline room to finish."""
    if resource is None:
        return
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    wanted = CHILD_STACK_BYTES
    if hard != resource.RLIM_INFINITY:
        wanted = min(wanted, hard)
    if soft != resource.RLIM_INFINITY and soft < wanted:
        resource.setrlimit(resource.RLIMIT_STACK, (wanted, hard))


class RunResult:
    def __init__(self, status, detail="", files=(), stdout=b""):
        self.status = status
        self.detail = detail
        self.files = tuple(files)
        self.stdout = stdout

    def description(self):
        if self.status == "completed":
            return self.status
        return "%s%s" % (self.status,
                         (" (%s)" % self.detail) if self.detail else "")


def cnf_for(stp, query, flag, workdir):
    """Solve `query` with priming on or off and retain its exact outcome."""
    out = os.path.join(workdir, flag)
    os.makedirs(out, exist_ok=True)

    try:
        done = subprocess.run(
            [stp, "--array-equality", "--prime-memos", flag, "--output-CNF",
             "--SMTLIB2", query],
            cwd=out, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            timeout=TIMEOUT,
            preexec_fn=raise_child_stack_limit if resource else None)
    except subprocess.TimeoutExpired:
        return RunResult("timeout", "%ds" % TIMEOUT)

    if done.returncode != 0:
        return RunResult("exit", str(done.returncode), stdout=done.stdout)
    return RunResult("completed", files=sorted(os.listdir(out)),
                     stdout=done.stdout)


def query_selected(query, query_dir, features):
    """Whether this lit query is a positive test enabled in this build."""
    with open(query, errors="ignore") as handle:
        lines = handle.readlines()

    commands = []
    requirements = []
    for line in lines:
        run = re.match(r'^\s*;\s*RUN:\s*(.*)$', line)
        if run and "%solver" in run.group(1):
            commands.append(run.group(1).strip())
        required = re.match(r'^\s*;\s*REQUIRES:\s*(.*)$', line)
        if required:
            requirements.extend(piece.strip() for piece in
                                required.group(1).split(","))

    if commands and all(command.startswith("not %solver")
                        for command in commands):
        return False, "negative test"

    relative = os.path.relpath(query, query_dir)
    if ("fp-tests" in relative.split(os.sep) and
            "floating-point" not in features):
        return False, "floating-point is disabled"

    for requirement in requirements:
        if not requirement:
            continue
        if requirement.startswith("!"):
            if requirement[1:] in features:
                return False, "requires " + requirement
        elif requirement not in features:
            return False, "requires " + requirement

    return True, ""


def comparison_problem(on, off, workdir):
    """None for an exact completed pair, otherwise its failure category."""
    if on.status != "completed" or off.status != "completed":
        if ((on.status, on.detail) != (off.status, off.detail)):
            return "asymmetric: on %s, off %s" % (
                on.description(), off.description())
        return "newly incomparable: both %s" % on.description()

    differences = []
    if on.stdout != off.stdout:
        differences.append("stdout")
    if on.files != off.files:
        differences.append("CNF file set")

    common = sorted(set(on.files) & set(off.files))
    _, mismatch, errors = filecmp.cmpfiles(
        os.path.join(workdir, "1"), os.path.join(workdir, "0"),
        common, shallow=False)
    if mismatch or errors:
        differences.append("CNF contents")

    if differences:
        return "different " + ", ".join(differences)
    return None


def main():
    if len(sys.argv) < 3:
        print("usage: prime-memos-differential.py <stp binary> <query dir> "
              "[available-feature ...]")
        return 2

    stp, query_dir = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    features = set(sys.argv[3:])
    if not os.path.isfile(stp) or not os.access(stp, os.X_OK):
        print("no stp binary at %s -- skipping" % stp)
        return 77 # ctest treats this as "skipped".

    queries = []
    excluded = []
    for root, _, files in os.walk(query_dir):
        for filename in sorted(files):
            if not filename.endswith(".smt2"):
                continue
            query = os.path.join(root, filename)
            selected, reason = query_selected(query, query_dir, features)
            if selected:
                queries.append(query)
            else:
                excluded.append((query, reason))
    queries.sort()

    if not queries:
        print("no positive, applicable queries under %s -- skipping"
              % query_dir)
        return 77

    compared = 0
    problems = []

    for query in queries:
        workdir = tempfile.mkdtemp(prefix="prime-memos-")
        try:
            on = cnf_for(stp, query, "1", workdir)
            off = cnf_for(stp, query, "0", workdir)

            problem = comparison_problem(on, off, workdir)
            if on.status == "completed" and off.status == "completed":
                compared += 1
            if problem:
                problems.append((os.path.relpath(query, query_dir), problem))
        finally:
            shutil.rmtree(workdir, ignore_errors=True)

    print("compared %d positive, applicable queries (%d metadata-excluded)"
          % (compared, len(excluded)))

    if problems:
        print("priming on and off are not exactly comparable for:")
        for name, problem in problems[:20]:
            print("    %-60s %s" % (name, problem))
        if len(problems) > 20:
            print("    ... and %d more" % (len(problems) - 20))
        print("Every selected query must complete on both sides with the "
              "same stdout and CNF. See stp/Util/DagWalk.h.")
        return 1

    if compared == 0:
        print("nothing could be compared -- skipping")
        return 77

    return 0


if __name__ == "__main__":
    sys.exit(main())
