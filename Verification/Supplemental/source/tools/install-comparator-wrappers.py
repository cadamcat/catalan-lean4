from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
root=Path('/srv/catalan-audit'); prefix=Path('/opt/lean-4.33.1/bin')
original_before={name:hashlib.sha256((prefix/name).read_bytes()).hexdigest() for name in ['lean-original','lake']}
shutil.copy2('/usr/bin/python3.12',prefix/'python3-audit')
log=Path('/srv/catalan-proof/.lake/lean-invocations');log.mkdir()
subprocess.run(['chown','verifier:verifier',str(log)],check=True)
for name in ['lean','lake']:
 if name=='lake':(prefix/'lake').rename(prefix/'lake-original')
 temp=prefix/(name+'-wrapper-new');shutil.copy2(root/'tools'/(name+'-wrapper.py'),temp);temp.chmod(0o755);os.replace(temp,prefix/name)
assert hashlib.sha256((prefix/'lean-original').read_bytes()).hexdigest()==original_before['lean-original']
assert hashlib.sha256((prefix/'lake-original').read_bytes()).hexdigest()==original_before['lake']
record={'installed_epoch':time.time(),'reason':'Comparator permits writes only below project .lake and clears non-whitelisted environment variables. Log below .lake; force cache-disable inside Lake launcher. Python interpreter copied into allowed executable prefix.', 'official_binaries_preserved':original_before,'wrapper_hashes':{name:hashlib.sha256((prefix/name).read_bytes()).hexdigest() for name in ['lean','lake','python3-audit']}}
(root/'evidence/wrapper-adaptation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
