from pathlib import Path
import datetime
import json
import subprocess
import sys
import time

root=Path('/srv/catalan-audit')
proof=Path('/srv/catalan-proof')
path='/opt/lean-4.33.1/bin:/opt/catalan-checkers:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'
env=['runuser','-u','verifier','--','env','XDG_RUNTIME_DIR=/run/user/2000','DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/2000/bus','PATH='+path]
settings={'PATH':path,'LAKE_NO_CACHE':'true','LAKE_ARTIFACT_CACHE':'false','MATHLIB_NO_CACHE_ON_UPDATE':'1','LAKE_CACHE_DIR':'','LEAN_NUM_THREADS':'16'}

def stage(name, command, seconds):
    unit='catalan-source-'+name
    argv=env+['systemd-run','--user','--unit='+unit,'--pty','--wait',
        '--property=RestrictAddressFamilies=~AF_UNIX','--property=NoNewPrivileges=yes',
        '--property=MemoryMax=112G','--property=RuntimeMaxSec='+str(seconds)]
    for key,value in settings.items(): argv+=['-E',key+'='+value]
    argv+=['--working-directory='+str(proof),'--',*command]
    start=time.time()
    info={'stage':name,'argv':argv,'started_epoch':start,
          'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (root/'evidence'/f'{name}-started.json').write_text(json.dumps(info,indent=2)+'\n')
    print('START '+name,flush=True)
    with (root/'logs'/f'{name}.log').open('w') as log:
        p=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL)
        time.sleep(2)
        props=subprocess.run(env+['systemctl','--user','show',unit+'.service','--property=RestrictAddressFamilies,NoNewPrivileges,MemoryMax,RuntimeMaxUSec,MainPID,ActiveState,SubState,ExecStart'],capture_output=True,text=True)
        (root/'evidence'/f'{name}-unit.txt').write_text(props.stdout+props.stderr)
        # Very short commands can finish before systemd's query; main builds remain observable.
        if p.poll() is None:
            assert 'RestrictAddressFamilies=~AF_UNIX' in props.stdout
        rc=p.wait(timeout=seconds+120)
    info.update(exit_code=rc,ended_epoch=time.time(),elapsed_seconds=time.time()-start)
    (root/'evidence'/f'{name}-result.json').write_text(json.dumps(info,indent=2)+'\n')
    (root/'logs'/f'{name}.exit').write_text(str(rc)+'\n')
    print('END '+name+' exit='+str(rc),flush=True)
    if rc: raise SystemExit(rc)

assert json.loads((root/'evidence/preparation.json').read_text())['no_prebuilt_package_oleans']
assert json.loads((root/'evidence/socket-probes-result.json').read_text())['effective_properties_verified']
stage('mathlib',['lake','--no-cache','--no-ansi','--verbose','build','Mathlib'],14400)
assert not list((proof/'.lake/build').rglob('*.olean')), 'Submitted library compiled before comparator'
stage('comparator',['lake','env','/opt/catalan-checkers/comparator',str(root/'audit/config.json')],5400)
stage('verify',['bash','scripts/verify.sh'],3600)
stage('all-vendor',['lake','--no-cache','--no-ansi','--verbose','build','ClassFieldTheory','ValuedFieldTheory','GaloisCohomology'],1800)
stage('official-audit',['python3',str(root/'tools/audit.py'),'run',str(root/'audit/targets.json'),'--out',str(root/'results/official-audit'),'--lake','/opt/lean-4.33.1/bin/lake','--timeout','1800'],2100)
stage('replay',['bash','scripts/replay.sh'],1800)
(root/'evidence/stages-complete.json').write_text(json.dumps({'completed_epoch':time.time(),'all_stages_exit_zero':True},indent=2)+'\n')
print('ALL_SOURCE_REBUILD_STAGES_PASSED',flush=True)
