"""Compile a standalone exploration module with the existing analysis toolchain.
Preserve each attempt. No dependency installation and no changes to formal/.
"""
from pathlib import Path
from datetime import datetime
import os,sys,re,json,hashlib,subprocess,argparse
sys.stdout.reconfigure(encoding='utf-8')
p=argparse.ArgumentParser();p.add_argument('module');p.add_argument('--project',type=Path,required=True)
p.add_argument('--cache',action='store_true');p.add_argument('--attempt',required=True)
a=p.parse_args();R=Path(__file__).resolve().parent;P=a.project.resolve()
src=R/'lean'/f'{a.module}.lean';(R/'evidence').mkdir(exist_ok=True);(R/'build').mkdir(exist_ok=True)
source_bytes=src.read_bytes();before_sha=hashlib.sha256(source_bytes).hexdigest()
s=source_bytes.decode('utf-8');expected=re.findall(r'^#print axioms (\S+)',s,re.M)
assert expected
assert not re.search(r'\b(sorry|admit|native_decide)\b',s)
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(R/'build'),str(P/'research/exploration/phase7/build'),str(P/'research/exploration/phase6/build'),str(P/'research/exploration/phase5/build'),str(P/'research/exploration/phase4/build'),str(P/'research/exploration/phase3/build'),str(P/'research/exploration/phase2/build')])
cmd=[str(P/'formal/.tools/lean-4.35.0-rc4-windows/bin/lake.exe'),'env','lean','--trust=0','--root='+str(src.parent)]
if a.cache:cmd+=['-o',str(R/'build'/f'{a.module}.olean')]
cmd+=[str(src)]
prefix=R/'evidence'/f'{a.module}-{a.attempt}'
assert not prefix.with_suffix('.json').exists(), 'Attempt label already used; preserve prior evidence.'
(R/'evidence'/f'{a.module}-{a.attempt}.source.lean').write_bytes(source_bytes)
run=subprocess.run(cmd,cwd=P/'formal/analysis',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
prefix=R/'evidence'/f'{a.module}-{a.attempt}';log=prefix.with_suffix('.log');log.write_bytes(run.stdout)
t=run.stdout.decode('utf-8',errors='replace')
actual=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",t)
actual_names=[n.split('.')[-1] for n in actual]
expected_names=[n.split('.')[-1] for n in expected]
axioms=set()
for entry in re.findall(r'depends on axioms:\s*\[([^]]*)\]',t,re.S):axioms.update(x.strip() for x in entry.split(',') if x.strip())
source_unchanged=hashlib.sha256(src.read_bytes()).hexdigest()==before_sha
passed=source_unchanged and run.returncode==0 and actual_names==expected_names and axioms<={'propext','Classical.choice','Quot.sound'}
meta={'checked_at':datetime.now().astimezone().isoformat(),'module':a.module,'exit_code':run.returncode,
      'trust_level':0,'checks_passed':passed,'source_sha256':before_sha,'source_unchanged_during_build':source_unchanged,
      'log_sha256':hashlib.sha256(run.stdout).hexdigest(),'command':cmd,'cwd':str(P/'formal/analysis'),
      'named_declarations':actual,'expected_prints':expected,'axioms_seen':sorted(axioms)}
if a.cache and passed:meta['olean_sha256']=hashlib.sha256((R/'build'/f'{a.module}.olean').read_bytes()).hexdigest()
prefix.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
print(t);print(json.dumps({k:v for k,v in meta.items() if k not in ['named_declarations','expected_prints']}))
sys.exit(0 if passed else 1)
