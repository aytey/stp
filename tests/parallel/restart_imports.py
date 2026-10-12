#!/usr/bin/env python3
"""Compare the import schedules' answers and counters on all four roots."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import sanitizer

binary, driver = map(lambda p: str(Path(p).resolve()), sys.argv[1:3])
sanitizer.install(binary, driver)
cpus = sorted(os.sched_getaffinity(0))[:4]
if len(cpus) < 4:
    print('SKIP: import schedule test needs four CPUs')
    sys.exit(0)
os.sched_setaffinity(0, cpus)
probe = subprocess.run([binary, '-j4', '--import-at-restarts'],
                       input='(set-logic QF_BV)(check-sat)',
                       text=True, capture_output=True, timeout=10)
if probe.returncode == 2 and ('clause-import' in probe.stderr or
                              'restart-aligned' in probe.stderr):
    print('SKIP: backend has no restart-aligned import')
    sys.exit(0)
assert probe.returncode == 10, probe


def factoring(product):
    return ('(set-logic QF_BV)(declare-const x (_ BitVec 40))'
            '(declare-const y (_ BitVec 40))'
            f'(assert (= (bvmul x y) (_ bv{product} 40)))'
            '(assert (bvugt x (_ bv1 40)))(assert (bvugt y (_ bv1 40)))'
            '(assert (bvult x (_ bv65536 40)))(assert (bvult y (_ bv65536 40)))'
            '(check-sat)')


with tempfile.TemporaryDirectory(prefix='stpp-restarts-') as directory:
    stats = Path(directory) / 'stats.json'
    observed = 0
    for aligned in [False, True]:
        for product, answer, code in [(46337 * 46327, 'sat', 10),
                                     (2147483647, 'unsat', 20)]:
            args = [driver, '-j4', '--control', 'batch-all', '--exchange-interval', '16',
                    '--timeout', '40', '--stats-json', str(stats)]
            if aligned:
                args.append('--import-at-restarts')
            p = subprocess.run(args, input=factoring(product), text=True,
                               capture_output=True, timeout=45)
            assert (p.returncode, p.stdout.strip()) == (code, answer), p
            report = json.loads(stats.read_text())
            assert report['cleanup_complete'], report
            assert report['import_at_restarts'] == aligned, report
            assert len(report['children']) == 4, report
            for child in report['children']:
                data = child['report']
                assert data['answer'] == answer, child
                exchange = data['exchange']
                polls = exchange['backend_polls']
                scheduled = sum(exchange['backend_' + name] for name in
                                ['import-at-restart', 'import-at-root', 'import-forced'])
                assert scheduled == (polls if aligned else 0), exchange
                if child['slot'] == 0:
                    assert polls == 0, exchange
                elif aligned:
                    observed += scheduled
    assert observed > 0, 'aligned mode must import during actual search'

p = subprocess.run([binary, '-j1', '--import-at-restarts'],
                   input='(check-sat)', text=True, capture_output=True, timeout=5)
assert p.returncode == 2 and '--import-at-restarts' in p.stderr, p
print('PASS: periodic and restart-aligned imports preserve all root answers')
