"""Compile a revision module with the locked Lean binary and isolated outputs."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys, time
sys.stdout.reconfigure(encoding='utf-8')
ROOT=Path(__file__).resolve().parent
PROJECT=Path('D:/MyWorks/Math')
LEAN=PROJECT/'formal/.tools/lean-4.35.0-rc4-windows/bin/lean.exe'
p=argparse.ArgumentParser()
p.add_argument('module')
p.add_argument('--source-dir', type=Path, default=ROOT/'lean')
p.add_argument('--cache', type=Path, default=ROOT/'build')
p.add_argument('--fresh-base', action='store_true')
a=p.parse_args()
src=a.source_dir/(a.module+'.lean'); a.cache.mkdir(parents=True,exist_ok=True)
(ROOT/'evidence').mkdir(exist_ok=True)
paths=[a.cache]
if a.fresh_base:
    paths += [ROOT/'fresh-base/analysis']
else:
    paths += [ROOT/'build',PROJECT/'formal/analysis/.lake/build/lib/lean',PROJECT/'formal/.lake/build/lib/lean']
paths += [q/'.lake/build/lib/lean' for q in (PROJECT/'formal/analysis/.lake/packages').iterdir() if q.is_dir()]
env=os.environ.copy(); env['LEAN_PATH']=';'.join(str(q) for q in paths)
cmd=[str(LEAN),'--trust=0','--root='+str(a.source_dir),'-o',str(a.cache/(a.module+'.olean')),str(src)]
start=time.time(); log=ROOT/'evidence'/(a.module+'.log')
with log.open('w',encoding='utf-8',newline='\n') as f:
    r=subprocess.run(cmd,cwd=PROJECT/'formal/analysis',env=env,stdout=f,stderr=subprocess.STDOUT)
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
text=log.read_text(encoding='utf-8')
meta={'module':a.module,'command':cmd,'exit_code':r.returncode,'seconds':time.time()-start,'source_sha256':sha(src),'log_sha256':sha(log),'trust_level':0,'fresh_project_base':a.fresh_base,'lean_path':env['LEAN_PATH'],'actual_axiom_outputs':re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",text),'source':str(src),'olean':str(a.cache/(a.module+'.olean'))}
if (a.cache/(a.module+'.olean')).exists():meta['olean_sha256']=sha(a.cache/(a.module+'.olean'))
(ROOT/'evidence'/(a.module+'-build.json')).write_text(json.dumps(meta,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:meta[k] for k in ['module','exit_code','seconds','source_sha256','log_sha256']},ensure_ascii=False))
print(text[-12000:])
sys.exit(r.returncode)
