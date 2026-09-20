from pathlib import Path
import json
import subprocess
import time

root = Path("/srv/catalan-audit")
env = ["runuser", "-u", "verifier", "--", "env", "XDG_RUNTIME_DIR=/run/user/2000", "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/2000/bus"]
probe = str(root / "audit/socket_probe.py")
with (root / "logs/socket-baseline.log").open("w") as log:
    baseline = subprocess.run(env + ["/usr/bin/python3", probe, "allowed"], stdout=log, stderr=subprocess.STDOUT)
assert baseline.returncode == 0, "socket baseline did not pass"
command = env + [
    "/usr/bin/systemd-run", "--user", "--unit=catalan-socket-probe", "--wait", "--pty",
    "--property=RestrictAddressFamilies=~AF_UNIX", "--property=NoNewPrivileges=yes",
    "/usr/bin/python3", probe, "blocked", "10",
]
(root / "evidence/socket-probe-argv.json").write_text(json.dumps(command, indent=2) + "\n")
with (root / "logs/socket-restricted.log").open("w") as log:
    process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    time.sleep(2)
    inspected = subprocess.run(env + ["systemctl", "--user", "show", "catalan-socket-probe.service", "--property=RestrictAddressFamilies,NoNewPrivileges,User,MainPID,ActiveState,SubState,ExecStart"], capture_output=True, text=True)
    (root / "evidence/socket-unit-properties.txt").write_text(inspected.stdout + inspected.stderr)
    exit_code = process.wait(timeout=40)
assert exit_code == 0, "restricted AF_UNIX probe did not pass"
assert "PROBE_PASSED=blocked" in (root / "logs/socket-restricted.log").read_text(), "restricted probe marker missing"
assert "RestrictAddressFamilies=~AF_UNIX" in inspected.stdout, "effective systemd restriction not observed"
assert "NoNewPrivileges=yes" in inspected.stdout, "effective no-new-privileges setting not observed"
(root / "evidence/socket-probes-result.json").write_text(json.dumps({"baseline_exit": baseline.returncode, "restricted_exit": exit_code, "effective_properties_verified": True}, indent=2) + "\n")
print("AF_UNIX_CONTROL_SUITE_PASSED")
