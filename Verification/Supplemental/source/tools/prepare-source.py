from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import time

root = Path('/srv/catalan-audit')
proof = Path('/srv/catalan-proof')
assert (root/'logs/bootstrap.exit').read_text().strip() == '0'
env = os.environ.copy()
env.update(PATH='/opt/lean-4.33.1/bin:/opt/catalan-checkers:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
           LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false', MATHLIB_NO_CACHE_ON_UPDATE='1',
           LAKE_CACHE_DIR='', LEAN_NUM_THREADS='16')

def run(args, cwd=None):
    print(json.dumps(args), flush=True)
    subprocess.run(args, cwd=cwd, env=env, check=True)

def clone(url, rev, path):
    path.mkdir(parents=True)
    run(['git', 'init', '-q', str(path)])
    run(['git', '-C', str(path), 'remote', 'add', 'origin', url])
    run(['git', '-C', str(path), 'fetch', '--depth=1', 'origin', rev])
    run(['git', '-C', str(path), 'checkout', '--detach', 'FETCH_HEAD'])
    assert subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip() == rev

clone('https://github.com/cadamcat/catalan-lean4', '897079dab4c8dc980cc9b98ab28fed846e4a756f', proof)
manifest = json.loads((proof/'lake-manifest.json').read_text())
for pkg in manifest['packages']:
    clone(pkg['url'], pkg['rev'], proof/'.lake/packages'/pkg['name'])

# Keep the official binary intact under a recorded name. Lake still finds the same sysroot.
lean = Path('/opt/lean-4.33.1/bin/lean')
original = lean.with_name('lean-original')
lean.rename(original)
shutil.copy2(root/'tools/lean-wrapper.py', lean)
lean.chmod(0o755)
(root/'invocations').mkdir()
run(['chmod', '0777', str(root/'invocations')])
for n in range(24):
    p=root/'invocations'/f'slot-{n}'
    p.touch(); p.chmod(0o666)
(root/'evidence/lean-binary.json').write_text(json.dumps({
    'official_binary_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
    'wrapper_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),
    'note':'Official Lean 4.33.1 executable preserved; wrapper adds --trust=0, -j2 and records actual argv. No package cache used.'}, indent=2)+'\n')

# Mathlib deliberately refuses to build this dependency's JS itself. Build its named
# upstream target first with that package's own configuration, without editing sources.
run(['lake','--no-cache','--no-ansi','build','widgetJsAll'], proof/'.lake/packages/proofwidgets')
packages = [proof] + [proof/'.lake/packages'/p['name'] for p in manifest['packages']]
identities=[]
for path in packages:
    state=subprocess.check_output(['git','-C',str(path),'status','--porcelain'],text=True)
    assert not state, (str(path),state)
    artifacts=list((path/'.lake/build').rglob('*.olean')) if (path/'.lake/build').exists() else []
    assert not artifacts, ('preexisting package library oleans',str(path),[str(p) for p in artifacts])
    identities.append({'path':str(path),'sha':subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip(),'clean':True,'library_oleans_before_build':0})
(root/'evidence/source-identities-before.json').write_text(json.dumps(identities,indent=2)+'\n')
assert not (proof/'.lake/build').exists()
for name in ['StrictChallenge.lean','StrictSolution.lean']:
    shutil.copy2(root/'audit'/name, proof/'Catalan'/name)

fingerprints={}
for path in packages:
    files=subprocess.check_output(['git','-C',str(path),'ls-files','-z']).decode().split('\0')
    for name in filter(None, files):
        p=path/name
        if p.is_file(): fingerprints[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
for p in [proof/'Catalan/StrictChallenge.lean', proof/'Catalan/StrictSolution.lean',root/'audit/config.json']:
    fingerprints[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
(root/'evidence/source-fingerprints-before.json').write_text(json.dumps(fingerprints,sort_keys=True,indent=2)+'\n')
run(['chown','-R','root:root',str(proof)])
run(['chmod','-R','go-w',str(proof)])
for path in packages:
    (path/'.lake').mkdir(exist_ok=True)
    run(['chown','verifier:verifier',str(path/'.lake')])
    (path/'.lake/build').mkdir(exist_ok=True)
    run(['chown','-R','verifier:verifier',str(path/'.lake/build')])
    config=path/'.lake/config'
    if config.exists(): run(['chown','-R','verifier:verifier',str(config)])
    run(['runuser','-u','verifier','--','git','config','--global','--add','safe.directory',str(path)])
for directory in [root/'results',proof/'verification-results']:
    directory.mkdir(exist_ok=True)
    run(['chown','verifier:verifier',str(directory)])
for binary in ['iptables','ip6tables']:
    run([binary,'-I','OUTPUT','1','-m','owner','--uid-owner','2000','-j','REJECT'])
(root/'evidence/preparation.json').write_text(json.dumps({'completed_epoch':time.time(),'no_prebuilt_package_oleans':True,'proofwidgets_js_built_from_source':True,'verifier_network_disabled':True,'source_files_fingerprinted':len(fingerprints)},indent=2)+'\n')
print('SOURCE_PREPARATION_PASSED',flush=True)
