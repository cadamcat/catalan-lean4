from pathlib import Path
import datetime
import json
import subprocess

root = Path("/srv/catalan-audit")
trusted_path = "/opt/lean-4.33.1/bin:/opt/catalan-checkers:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
env = ["runuser", "-u", "verifier", "--", "env", "XDG_RUNTIME_DIR=/run/user/2000", "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/2000/bus", "PATH=" + trusted_path]
records = []
for kind in ["positive", "wrong-statement", "extra-axiom"]:
    project = root / "audit/controls" / kind
    (project / "lake-manifest.json").write_text(json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [], "name": "ComparatorControl", "lakeDir": ".lake", "fixedToolchain": False}) + "\n")
    (project / ".lake").mkdir()
    subprocess.run(["chown", "verifier:verifier", str(project / ".lake")], check=True)
    command = env + ["systemd-run", "--user", "--unit=catalan-control-" + kind, "--wait", "--pty", "--property=RestrictAddressFamilies=~AF_UNIX", "--property=NoNewPrivileges=yes", "--property=MemoryMax=4G", "--property=RuntimeMaxSec=180", "-E", "PATH=" + trusted_path, "--working-directory=" + str(project), "--", "bash", "-c", "lake env /opt/catalan-checkers/comparator " + str(project / "config.json")]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (root / "logs" / ("control-" + kind + ".log")).open("w") as log:
        log.write("START=" + started + "\nCOMMAND=" + json.dumps(command) + "\n")
        log.flush()
        result = subprocess.run(command, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT, timeout=200)
        log.write("\nEXIT=" + str(result.returncode) + "\n")
    record = {"control": kind, "exit_code": result.returncode, "started_at": started, "ended_at": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    records.append(record)
    print(json.dumps(record), flush=True)
(root / "evidence/comparator-controls.json").write_text(json.dumps(records, indent=2) + "\n")
assert records[0]["exit_code"] == 0, "positive comparator control failed"
assert records[1]["exit_code"] != 0, "wrong-statement comparator control was accepted"
assert records[2]["exit_code"] != 0, "extra-axiom comparator control was accepted"
