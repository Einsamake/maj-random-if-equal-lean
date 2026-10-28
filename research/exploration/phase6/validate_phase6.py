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
for rel,h in load(R/'notes/phase5-freeze.json').items():assert sha(R.parent/rel)==h,rel
for n,h in {'DirectedNetworkComparison':'e1eb401a053c70e20a295f1cf0d22ced4e1b3b7a5ec52b4714d87a7c87a1182a','FullBlockThreshold':'1910b52305e593410d0c190f17e2fafa9f47cfb24acf9b08ad45bce2aeec8d79'}.items():assert sha(R.parent/'lean'/f'{n}.lean')==h
modules=['ResponseKernelCalculus','TankResponse','GeneralTankCdf','MeanRateOrder','CompletionTimeOrder','HiddenBranchWitness']
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
s,m,log,unified=check('Phase6Audit',spec['Phase6Audit'])
assert unified==all_names and len(unified)==len(set(unified))
reader=load(R/'reader-review.json')
assert reader['status']=='pass' and reader['unresolved_blockers']==[]
for rel,h in reader['reviewed_file_sha256'].items():assert sha(R/rel)==h,rel
fig=load(R/'figure-data.json')
for rel,h in fig['images'].items():assert sha(R/'images'/rel)==h
links=[]
for n in ['README.md']:
 s=(R/n).read_text(encoding='utf-8')
 assert not any(x in s for x in [r'\(',r'\)'])
 assert not [l for l in s.splitlines() if l.count('$')%2]
 for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',s):
  if target.startswith(('https://','http://','#')) or target=='validation.json':continue
  assert (R/unquote(target)).resolve().exists(),target
  links.append(target)
for file in R.glob('*.py'):ast.parse(file.read_text(encoding='utf-8'))
artifacts={q.relative_to(R).as_posix():sha(q) for q in sorted(R.rglob('*')) if q.is_file() and q.name!='validation.json' and 'build' not in q.relative_to(R).parts}
result={'checked_at':datetime.now().astimezone().isoformat(),'status':'PASS','mathematical_modules':len(modules),'audit_driver_modules':1,'named_declarations':len(all_names),'new_theorems':theorems,'modules':records,'unified_audit':{'source_sha256':m['source_sha256'],'log_sha256':sha(log),'actual_prints':len(unified),'trust_level':0,'exit_code':0},'reader_review':reader,'local_links_checked':len(links),'original_formal_sources_unchanged':len(base['all_formal_source_sha256']),'phase1_math_sources_unchanged':True,'prior_accepted_artifacts_unchanged':True,'sealed_original_zip_sha256':pack['sha256'],'artifact_sha256':artifacts,'claims':{'parameters':'a,b>0,e,f>=0,e+f>0, fixed rates, zero initial state and constant inlet1','constructed_actual_response_exists_and_satisfies_ODE':True,'actual_CDF_equals_response_for_all_parameters':True,'actual_CDF_positive_time_ODE':True,'f_order_on_actual_CDF_at_every_real_deadline':{'e_le_b':'nondecreasing','b_le_e':'nonincreasing','b_eq_e':'totalMeasure invariant in f'},'actual_mean_order_opposite_to_CDF_order':True,'hidden_branch_actual_probabilities':['1/3','1/2'],'hidden_branch_same_totalMeasure_different_sample_law':True,'strict_CDF_order_or_necessity_classification_proved':False,'new_field_or_novelty_certification':False,'reader_simulation_not_human_test':True}}
(R/'validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:result[k] for k in ['status','named_declarations','new_theorems','original_formal_sources_unchanged','local_links_checked']}))
