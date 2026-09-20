#!/usr/bin/python3
"""Record real Lean invocations; enforce trust=0 and bound elaborator concurrency."""
import fcntl
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

args = sys.argv[1:]
for arg in args:
    if arg.startswith('--trust=') and arg != '--trust=0':
        raise SystemExit('Refusing nonzero trust argument: ' + arg)
root = Path('/srv/catalan-audit/invocations')
root.mkdir(exist_ok=True)
source = any(arg.endswith('.lean') for arg in args)
lock = None
if source:
    while lock is None:
        for n in range(12):
            candidate = open(root / f'slot-{n}', 'a')
            try:
                fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
                lock = candidate
                break
            except BlockingIOError:
                candidate.close()
        if lock is None:
            time.sleep(0.1)
command = ['/opt/lean-4.33.1/bin/lean-original', '--trust=0', '-j2', *args]
start = time.time()
record = {'pid': os.getpid(), 'cwd': os.getcwd(), 'argv': command,
          'started_epoch': start, 'uid': os.getuid(), 'lean_path': os.getenv('LEAN_PATH'),
          'lake_no_cache': os.getenv('LAKE_NO_CACHE'),
          'lake_artifact_cache': os.getenv('LAKE_ARTIFACT_CACHE')}
path = root / f'{os.getpid()}-{time.time_ns()}.json'
path.write_text(json.dumps(record) + '\n')
result = subprocess.run(command)
record.update(exit_code=result.returncode, ended_epoch=time.time(),
              elapsed_seconds=time.time()-start,
              child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
path.write_text(json.dumps(record) + '\n')
sys.exit(result.returncode)
