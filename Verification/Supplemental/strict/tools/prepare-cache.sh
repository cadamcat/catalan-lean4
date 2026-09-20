#!/usr/bin/env bash
set -Eeuo pipefail
trap 'rc=$?; printf "%s\n" "$rc" > /srv/catalan-audit/logs/cache.exit; date -u +%FT%TZ > /srv/catalan-audit/logs/cache.ended; exit "$rc"' EXIT
date -u +%FT%TZ > /srv/catalan-audit/logs/cache.started
export PATH=/opt/lean-4.33.1/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
export XDG_CACHE_HOME=/srv/catalan-audit/trusted-cache
mkdir -p /srv/catalan-trusted-cache
cp /srv/catalan-proof/lean-toolchain /srv/catalan-trusted-cache/
python3 - <<'PY'
import json
from pathlib import Path
root=Path('/srv/catalan-trusted-cache')
manifest=json.loads(Path('/srv/catalan-proof/lake-manifest.json').read_text())
manifest['name']='TrustedMathlibBootstrap'
(root/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(root/'lakefile.toml').write_text('name = "TrustedMathlibBootstrap"\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\nrev = "v4.33.1"\n')
PY
cd /srv/catalan-trusted-cache
lake exe cache get
python3 - <<'PY'
from pathlib import Path
import json,subprocess
root=Path('/srv/catalan-trusted-cache')
manifest=json.loads(Path('/srv/catalan-proof/lake-manifest.json').read_text())
records=[]
for pkg in manifest['packages']:
    path=root/'.lake/packages'/pkg['name']
    sha=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    state=subprocess.check_output(['git','-C',str(path),'status','--porcelain'],text=True)
    assert sha==pkg['rev'], (pkg['name'],sha,pkg['rev'])
    assert not state, (pkg['name'],state)
    records.append({'name':pkg['name'],'sha':sha,'url':pkg['url'],'clean':True})
Path('/srv/catalan-audit/evidence/dependency-identities.json').write_text(json.dumps(records,indent=2)+'\n')
assert not Path('/srv/catalan-proof/.lake').exists(), 'Submitted project acquired build state too soon'
Path('/srv/catalan-proof/.lake').mkdir()
(root/'.lake/packages').rename('/srv/catalan-proof/.lake/packages')
assert not Path('/srv/catalan-proof/.lake/build').exists()
print('TRUSTED_CACHE_READY; no submitted project module has been compiled')
PY
