"""Bind actual standard-kernel logs, independent reviews, reader evidence and frozen work."""
from pathlib import Path
from datetime import datetime
import argparse,ast,json,re,hashlib
from urllib.parse import unquote
p=argparse.ArgumentParser();p.add_argument('--project',type=Path,required=True)
a=p.parse_args();P=a.project.resolve();R=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
allowed={'propext','Classical.choice','Quot.sound'}
base=load(P/'formal/audit/original-theta-independent-final-binding-evidence.json')
for rel,h in base['all_formal_source_sha256'].items():assert sha(P/'formal'/rel)==h,rel
pack=load(P/'formal/audit/package-validation.json')
assert sha(P/'deliverables/Lean形式化材料_2026-10-26.zip')==pack['sha256']
for rel,h in load(R.parent/'phase5/notes/prior-accepted-freeze.json').items():assert sha(R.parent/rel)==h,rel
for rel,h in load(R.parent/'phase6/notes/phase5-freeze.json').items():assert sha(R.parent/rel)==h,rel
for rel,h in load(R.parent/'phase7/notes/phase6-freeze.json').items():assert sha(R.parent/rel)==h,rel
for rel,h in load(R/'notes/phase7-freeze.json').items():assert sha(R.parent/rel)==h,rel
for n,h in {'DirectedNetworkComparison':'e1eb401a053c70e20a295f1cf0d22ced4e1b3b7a5ec52b4714d87a7c87a1182a','FullBlockThreshold':'1910b52305e593410d0c190f17e2fafa9f47cfb24acf9b08ad45bce2aeec8d79'}.items():assert sha(R.parent/'lean'/f'{n}.lean')==h
modules=['CoordinateResponseOrder','RateBoxMaximum']
spec=load(R/'audit-selection.json')
all_names=[];records={};theorems=0

def check(name,label):
 src=R/'lean'/f'{name}.lean';s=src.read_text(encoding='utf-8')
 meta=load(R/'evidence'/f'{label}.json');log=R/'evidence'/f'{label}.log'
 assert meta['exit_code']==0 and meta['trust_level']==0 and meta['checks_passed']
 assert meta['source_unchanged_during_build'] and '--trust=0' in meta['command']
 assert sha(src)==meta['source_sha256'] and sha(log)==meta['log_sha256']
 assert sha(R/'evidence'/f'{label}.source.lean')==sha(src)
 t=log.read_text(encoding='utf-8');expected=re.findall(r'^#print axioms (\S+)',s,re.M)
 actual=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",t)
 assert expected==actual==meta['named_declarations'] and not re.search(r'\berror:|sorryAx',t),name
 for ax in re.findall(r'depends on axioms:\s*\[([^]]*)\]',t,re.S):assert {x.strip() for x in ax.split(',') if x.strip()}<=allowed
 code=re.sub(r'/-.*?-/', '',s,flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe|constant)\b',code,re.M)
 assert sha(R/'build'/f'{name}.olean')==meta['olean_sha256'],name
 return s,meta,log,actual

reviews=load(R/'source-review-binding.json')
assert reviews['status']=='PASS' and reviews['blocking_findings']==[]
for name in modules:
 label=spec[name];s,m,log,names=check(name,label)
 rr=reviews['modules'][name]
 assert rr['source_sha256']==sha(R/'lean'/f'{name}.lean') and rr['log_sha256']==sha(log)
 review=R/rr['review_file'];assert sha(review)==rr['review_sha256']
 j=load(review);assert j['verdict'].startswith('PASS') and j['blocking_findings']==[]
 assert m['source_sha256'] in review.read_text(encoding='utf-8').lower()
 count=len(re.findall(r'^\s*(?:@\[[^\n]*\]\s*)*(?:theorem|lemma)\s+',s,re.M));theorems+=count;all_names+=names
 records[name]={'source_sha256':m['source_sha256'],'log_sha256':sha(log),'record_sha256':sha(R/'evidence'/f'{label}.json'),'review_sha256':sha(review),'named':len(names),'theorems':count,'olean_sha256':m['olean_sha256']}
s,m,log,unified=check('Phase8Audit',spec['Phase8Audit'])
assert unified==all_names and len(unified)==len(set(unified))

artifacts={q.relative_to(R).as_posix():sha(q) for q in sorted(R.rglob('*')) if q.is_file() and q.name not in ['math-validation.json','validation.json'] and 'build' not in q.relative_to(R).parts}
result={'checked_at':datetime.now().astimezone().isoformat(),'status':'PASS_MATHEMATICS_ONLY','stage_complete':False,'human_materials_and_reader_cycle_pending':True,'mathematical_modules':len(modules),'named_declarations':len(all_names),'new_theorems':theorems,'modules':records,'unified_audit':{'source_sha256':m['source_sha256'],'log_sha256':sha(log),'actual_prints':len(unified),'trust_level':0,'exit_code':0},'original_formal_sources_unchanged':len(base['all_formal_source_sha256']),'sealed_original_zip_sha256':pack['sha256'],'prior_accepted_artifacts_unchanged':True,'artifact_sha256':artifacts,'scope':'Fixed nonnegative independent ratebox with positive lowera,b andelo+flo; constantinlet1, zero initialstate; same actual probability corner greatest at every nonnegative deadline. No timevarying rates, variableinputs, zero-exit realprobabilitylaw or physicalflow-volume uncertainty claim.'}
(R/'math-validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:result[k] for k in ['status','stage_complete','named_declarations','new_theorems']}))
