"""Compile all revision modules against the fresh project replay and audit names."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,time
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent
base=R/'evidence/base-replay/replay.json'
while True:
    try: b=json.loads(base.read_text(encoding='utf-8'))
    except (FileNotFoundError,json.JSONDecodeError):time.sleep(5);continue
    if b['status']=='FAILED':raise RuntimeError('Base replay failed')
    if b['status']=='PASS':break
    time.sleep(5)
cache=R/'final-build'
sequence=[('FullBlockThreshold',R/'lean/dependencies'),('ImprovedOriginalLower',R/'lean/dependencies')]
sequence += [(s,R/'lean') for s in ['OriginalRecoveryResults','SharpRecoveryTail','SharpFailureRate','RecoveryMoments','OriginalConsequences']]
records=[];all_names=[];new_names=[]
for name,folder in sequence:
    cmd=[sys.executable,str(R/'run_lean.py'),name,'--source-dir',str(folder),'--cache',str(cache),'--fresh-base']
    r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    print(r.stdout[-2500:],flush=True)
    if r.returncode:raise RuntimeError(name+' failed')
    meta=json.loads((R/'evidence'/(name+'-build.json')).read_text(encoding='utf-8'))
    source=(folder/(name+'.lean')).read_text(encoding='utf-8')
    ns=re.search(r'^namespace (\S+)',source,re.M).group(1)
    declared=[ns+'.'+n for n in re.findall(r'^(?:noncomputable )?(?:def|theorem|lemma|abbrev) (\w+)',source,re.M)]
    printed=meta['actual_axiom_outputs'];assert declared==printed,(name,declared,printed)
    text=(R/'evidence'/(name+'.log')).read_text(encoding='utf-8')
    assert not re.search(r'\berror:|sorryAx',text)
    for x in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S):
        assert {t.strip() for t in x.split(',') if t.strip()}<={'propext','Classical.choice','Quot.sound'}
    all_names.extend(declared)
    if folder==R/'lean':new_names.extend(declared)
    records.append(meta)
audit=R/'lean/RevisionAxioms.lean'
audit.write_text('import OriginalConsequences\nimport SharpFailureRate\n\n'+'\n'.join('#print axioms '+n for n in all_names)+'\n',encoding='utf-8')
cmd=[sys.executable,str(R/'run_lean.py'),'RevisionAxioms','--cache',str(cache),'--fresh-base']
r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8');print(r.stdout[-2500:],flush=True)
assert r.returncode==0
meta=json.loads((R/'evidence/RevisionAxioms-build.json').read_text(encoding='utf-8'))
assert meta['actual_axiom_outputs']==all_names
text=(R/'evidence/RevisionAxioms.log').read_text(encoding='utf-8')
assert 'sorryAx' not in text and 'error:' not in text
for x in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S):
    assert {t.strip() for t in x.split(',') if t.strip()}<={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
result={'status':'PASS','trust_level':0,'new_modules':5,'new_named_declarations':len(new_names),'copied_existing_modules':2,'existing_dependency_declarations':len(all_names)-len(new_names),'aggregate_axiom_outputs':len(all_names),'fresh_project_replay_sha256':sha(base),'external_dependencies':'locked installed Lean/mathlib reused; project sources freshly compiled','modules':records,'aggregate':meta,'new_declarations':new_names,'allowed_axioms':['propext','Classical.choice','Quot.sound']}
(R/'evidence/unified-build.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:result[k] for k in ['status','new_modules','new_named_declarations','aggregate_axiom_outputs']},ensure_ascii=False),flush=True)
