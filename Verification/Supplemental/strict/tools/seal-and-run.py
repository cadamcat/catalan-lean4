from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

root = Path("/srv/catalan-audit")
proof = Path("/srv/catalan-proof")
stamp = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
assert (root / "logs/bootstrap-tools.exit").read_text().strip() == "0"
assert (root / "logs/cache.exit").read_text().strip() == "0"
assert json.loads((root / "evidence/socket-probes-result.json").read_text())["effective_properties_verified"]
assert subprocess.check_output(["git", "-C", str(proof), "rev-parse", "HEAD"], text=True).strip() == "897079dab4c8dc980cc9b98ab28fed846e4a756f"
assert not subprocess.check_output(["git", "-C", str(proof), "status", "--porcelain"], text=True).strip()
assert not (proof / ".lake/build").exists(), "submitted project has build outputs before comparator"
for name in ["StrictChallenge.lean", "StrictSolution.lean"]:
    (proof / "Catalan" / name).write_bytes((root / "audit" / name).read_bytes())
subprocess.run(["chown", "-R", "root:root", str(proof)], check=True)
subprocess.run(["chmod", "-R", "go-w", str(proof)], check=True)
subprocess.run(["chown", "-R", "verifier:verifier", str(proof / ".lake")], check=True)
subprocess.run(["chmod", "-R", "u+rwX", str(proof / ".lake")], check=True)
subprocess.run(["runuser", "-u", "verifier", "--", "git", "config", "--global", "--add", "safe.directory", str(proof)], check=True)
trusted = [proof / "Catalan/StrictChallenge.lean", proof / "Catalan/StrictSolution.lean", proof / "lakefile.toml", proof / "lake-manifest.json", proof / "lean-toolchain", root / "audit/config.json"]
trusted += sorted(Path("/opt/catalan-checkers").iterdir())
fingerprints = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in trusted}
(root / "evidence/trusted-inputs-before.json").write_text(json.dumps(fingerprints, indent=2) + "\n")
probe = r'''
import os,json
paths=json.loads(__import__('sys').argv[1])
assert os.getuid()==2000
for path in paths:
    assert not os.access(path,os.W_OK), 'trusted file writable: '+path
    assert not os.access(os.path.dirname(path),os.W_OK), 'trusted parent writable: '+path
    try:
        fd=os.open(path,os.O_WRONLY|os.O_APPEND)
    except PermissionError:
        pass
    else:
        os.close(fd)
        raise AssertionError('trusted file opened for writing: '+path)
assert os.access('/srv/catalan-proof/.lake',os.W_OK)
print('TRUSTED_FILES_AND_PARENTS_WRITE_DENIED; BUILD_DIRECTORY_WRITABLE')
'''
checked = subprocess.run(["runuser", "-u", "verifier", "--", "python3", "-c", probe, json.dumps(list(fingerprints))], capture_output=True, text=True)
(root / "logs/trusted-input-permissions.log").write_text(checked.stdout + checked.stderr)
checked.check_returncode()
for binary in ["iptables", "ip6tables"]:
    subprocess.run([binary, "-I", "OUTPUT", "1", "-m", "owner", "--uid-owner", "2000", "-j", "REJECT"], check=True)
network = subprocess.run(["runuser", "-u", "verifier", "--", "curl", "--noproxy", "*", "--max-time", "8", "--fail", "https://github.com"], capture_output=True, text=True)
(root / "logs/verifier-network-off.log").write_text("EXIT=" + str(network.returncode) + "\n" + network.stdout + network.stderr)
assert network.returncode != 0, "verifier still has outbound network"
trusted_path = "/opt/lean-4.33.1/bin:/opt/catalan-checkers:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
env = ["runuser", "-u", "verifier", "--", "env", "XDG_RUNTIME_DIR=/run/user/2000", "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/2000/bus", "PATH=" + trusted_path]
command = env + [
    "systemd-run", "--user", "--unit=catalan-strict-comparator", "--pty", "--wait",
    "--property=RestrictAddressFamilies=~AF_UNIX", "--property=NoNewPrivileges=yes",
    "--property=MemoryMax=48G", "--property=RuntimeMaxSec=7200",
    "-E", "PATH=" + trusted_path,
    "--working-directory=" + str(proof), "--", "bash", "-c",
    "lake env /opt/catalan-checkers/comparator /srv/catalan-audit/audit/config.json",
]
(root / "evidence/comparator-argv.json").write_text(json.dumps(command, indent=2) + "\n")
before = {"started_at": stamp(), "proof_head": "897079dab4c8dc980cc9b98ab28fed846e4a756f", "no_project_build_directory": True, "first_submitted_module_build": "protected comparator invocation", "trusted_cache_preparation": "separate TrustedMathlibBootstrap project", "source_status": subprocess.check_output(["git", "-C", str(proof), "status", "--porcelain"], text=True)}
(root / "evidence/first-submitted-execution.json").write_text(json.dumps(before, indent=2) + "\n")
with (root / "logs/comparator.log").open("w") as log:
    log.write("START_UTC=" + before["started_at"] + "\n")
    log.write("COMMAND=" + json.dumps(command) + "\n")
    log.flush()
    process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
    time.sleep(2)
    props = subprocess.run(env + ["systemctl", "--user", "show", "catalan-strict-comparator.service", "--property=RestrictAddressFamilies,NoNewPrivileges,MemoryMax,RuntimeMaxUSec,MainPID,ActiveState,SubState,ExecStart"], capture_output=True, text=True)
    (root / "evidence/comparator-unit-properties.txt").write_text(props.stdout + props.stderr)
    assert "RestrictAddressFamilies=~AF_UNIX" in props.stdout, "comparator unit lacks observed AF_UNIX restriction"
    exit_code = process.wait(timeout=7350)
    log.write("\nEXIT=" + str(exit_code) + "\nEND_UTC=" + stamp() + "\n")
after = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in trusted}
(root / "evidence/trusted-inputs-after.json").write_text(json.dumps(after, indent=2) + "\n")
result = {"exit_code": exit_code, "ended_at": stamp(), "trusted_inputs_unchanged": fingerprints == after}
(root / "evidence/comparator-result.json").write_text(json.dumps(result, indent=2) + "\n")
(root / "logs/comparator.exit").write_text(str(exit_code) + "\n")
assert fingerprints == after, "trusted input changed during comparator"
assert not subprocess.check_output(["git", "-C", str(proof), "diff", "--stat", "HEAD"], text=True).strip(), "tracked proof source changed"
print(json.dumps(result, indent=2))
sys.exit(exit_code)
