from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
root=Path('/srv/catalan-audit');prefix=Path('/opt/lean-4.33.1/bin')
shutil.copy2(root/'tools/lean-wrapper.py',prefix/'lean-audit.py')
for name in ['lean','lake']:
 target=prefix/(name+'-launcher-new')
 args=['gcc','-O2','-Wall','-Wextra']
 if name=='lake':args+=['-DLAKE_WRAPPER']
 args+=[str(root/'tools/tool-launcher.c'),'-o',str(target)]
 subprocess.run(args,check=True)
 os.replace(target,prefix/name)
record={'installed_epoch':time.time(),'reason':'landrun -ldd cannot discover ELF interpreter dependencies for shebang launchers. Use small ELF launchers; retain original compiler and Lake unchanged.', 'hashes':{name:hashlib.sha256((prefix/name).read_bytes()).hexdigest() for name in ['lean','lake','lean-audit.py','lean-original','lake-original']}}
(root/'evidence/elf-wrapper-install.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
