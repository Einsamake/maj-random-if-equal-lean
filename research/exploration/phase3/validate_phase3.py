"""Validate actual audits and freeze bindings; does not replace Lean builds."""
from pathlib import Path
from datetime import datetime
import argparse,ast,hashlib,json,re
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
phase2=P/'research/exploration/phase2'
assert sha(phase2/'validation.json')=='c201fa212f47f8b7204dfcd354b7fc35282c22d4ccb168072e8e317ae11d442b'
prior=load(phase2/'validation.json')
for rel,h in prior['artifact_sha256'].items():assert sha(phase2/rel)==h,rel
for n,h in {'DirectedNetworkComparison':'e1eb401a053c70e20a295f1cf0d22ced4e1b3b7a5ec52b4714d87a7c87a1182a','FullBlockThreshold':'1910b52305e593410d0c190f17e2fafa9f47cfb24acf9b08ad45bce2aeec8d79'}.items():
 assert sha(P/'research/exploration/lean'/f'{n}.lean')==h
spec=[
 ('EndpointTank','EndpointTank-final','endpoint-tank-source-review.json'),
 ('EndpointArithmetic','EndpointArithmetic-attempt3','endpoint-arithmetic-source-review.json'),
 ('EndpointCertificate','EndpointCertificate-final','endpoint-certificate-source-review.json'),
 ('ScaledEndpointEnvelope','ScaledEndpointEnvelope-final','scaled-endpoint-source-review.json')]
all_names=[];records={};theorems=0
def check(name,label):
 src=R/'lean'/f'{name}.lean';s=src.read_text(encoding='utf-8')
 meta=load(R/'evidence'/f'{label}.json');log=R/'evidence'/f'{label}.log'
 assert meta['exit_code']==0 and meta['trust_level']==0 and meta['checks_passed']
 assert '--trust=0' in meta['command'] and sha(src)==meta['source_sha256']
 assert sha(log)==meta['log_sha256']
 t=log.read_text(encoding='utf-8')
 expected=re.findall(r'^#print axioms (\S+)',s,re.M)
 actual=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",t)
 assert expected==actual and not re.search(r'\berror:|sorryAx',t),name
 for ax in re.findall(r'depends on axioms:\s*\[([^]]*)\]',t,re.S):
  assert {x.strip() for x in ax.split(',') if x.strip()}<=allowed
 code=re.sub(r'/-.*?-/', '',s,flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe|constant)\b',code,re.M)
 if 'olean_sha256' in meta:assert sha(R/'build'/f'{name}.olean')==meta['olean_sha256'],name
 return s,meta,log,actual
for name,label,review_name in spec:
 s,m,log,names=check(name,label)
 review=R/'notes'/review_name;j=load(review)
 assert j['verdict'].startswith('PASS') and j['blocking_findings']==[]
 assert m['source_sha256'] in review.read_text(encoding='utf-8').lower()
 count=len(re.findall(r'^theorem ',s,re.M));theorems+=count;all_names+=names
 records[name]={'source_sha256':m['source_sha256'],'log_sha256':sha(log),'record_sha256':sha(R/'evidence'/f'{label}.json'),'review_sha256':sha(review),'named':len(names),'theorems':count,'olean_sha256':m['olean_sha256']}
s,m,log,unified=check('Phase3Audit','Phase3Audit-final')
assert unified==all_names and len(unified)==len(set(unified))==57
assert theorems==47
dep=load(R/'evidence/RobustTankCertificate-dependency-cache.json')
assert dep['exit_code']==0 and dep['trust_level']==0 and dep['checks_passed']
assert dep['source_sha256']==sha(phase2/'lean/RobustTankCertificate.lean')
assert sha(R/'build/RobustTankCertificate.olean')==dep['olean_sha256']
reader=load(R/'reader-review.json')
assert reader['status']=='pass' and reader['unresolved_blockers']==[]
for rel,h in reader['reviewed_file_sha256'].items():assert sha(R/rel)==h,rel
fig=load(R/'figure-data.json')
for rel,h in fig['images'].items():assert sha(R/'images'/rel)==h
links=[]
for n in ['README.md','PROOF.md']:
 s=(R/n).read_text(encoding='utf-8')
 assert not any(x in s for x in [r'\(',r'\)'])
 assert not [l for l in s.splitlines() if l.count('$')%2]
 for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',s):
  if target.startswith(('https://','http://','#')) or target=='validation.json':continue
  assert (R/unquote(target)).resolve().exists(),target
  links.append(target)
for file in R.glob('*.py'):ast.parse(file.read_text(encoding='utf-8'))
artifacts={q.relative_to(R).as_posix():sha(q) for q in sorted(R.rglob('*'))
 if q.is_file() and q.name!='validation.json' and 'build' not in q.relative_to(R).parts}
result={'checked_at':datetime.now().astimezone().isoformat(),'status':'PASS',
 'mathematical_modules':4,'audit_driver_modules':1,'named_declarations':57,'new_theorems':47,
 'modules':records,'unified_audit':{'source_sha256':m['source_sha256'],'log_sha256':sha(log),'actual_prints':len(unified),'trust_level':0,'exit_code':0},
 'reader_review':reader,'local_links_checked':len(links),
 'original_formal_sources_unchanged':len(base['all_formal_source_sha256']),
 'phase1_math_sources_unchanged':True,'phase2_artifacts_unchanged':True,
 'sealed_original_zip_sha256':pack['sha256'],'artifact_sha256':artifacts,
 'claims':{'actual_maximum_curve':True,'exact_maximum_at_check_time':'p(exp(-(21/19)*log2))',
 'rational_upper_not_claimed_attained':'7425545410773/32000000000000 <233/1000',
 'general_cap':'fixed C>=0, fixed nonnegative rates bounded by(C,2C,C,3C), includes C=0',
 'given_classical_solutions_only':True,'time_varying_coefficients':False,
 'human_testing_or_new_field_certification':False}}
(R/'validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:result[k] for k in ['status','named_declarations','new_theorems','original_formal_sources_unchanged','local_links_checked']}))

