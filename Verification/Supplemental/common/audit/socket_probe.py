import errno
import json
import os
import socket
import sys
import time

mode = sys.argv[1]
assert mode in {"allowed", "blocked"}
assert os.getuid() == 2000, "probe must run as the nonprivileged verifier"
results = {}
for name, family in [("AF_INET", socket.AF_INET), ("AF_UNIX", socket.AF_UNIX)]:
    try:
        sock = socket.socket(family, socket.SOCK_STREAM)
        sock.close()
        results[name] = {"created": True}
    except OSError as error:
        results[name] = {"created": False, "errno": error.errno, "error": str(error)}
status = open("/proc/self/status").read().splitlines()
record = {
    "mode": mode,
    "uid": os.getuid(),
    "groups": os.getgroups(),
    "results": results,
    "process_restrictions": [line for line in status if line.startswith(("NoNewPrivs:", "Seccomp:", "Seccomp_filters:"))],
    "invocation_id": os.environ.get("INVOCATION_ID"),
}
print(json.dumps(record, indent=2), flush=True)
assert results["AF_INET"]["created"], "AF_INET positive control failed"
if mode == "allowed":
    assert results["AF_UNIX"]["created"], "AF_UNIX baseline failed before restriction"
else:
    assert not results["AF_UNIX"]["created"], "AF_UNIX restriction did not block socket creation"
    assert results["AF_UNIX"]["errno"] in {errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES}, "unexpected AF_UNIX failure"
print("PROBE_PASSED=" + mode, flush=True)
time.sleep(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
