"""Bind actual four-module audits, frozen baselines and simulated reader.
This script never substitutes metadata checks for a new Lean build.
"""
from pathlib import Path
from datetime import datetime
import argparse,ast,hashlib,json,re
from urllib.parse import unquote
p=argparse.ArgumentParser();p.add_argument('--project',type=Path,required=True)
a=p.parse_args();P=a.project.resolve();R=Path(__file__).resolve().parent
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
load=lambda x:json.loads(x.read_text(encoding='utf-8-sig'))
old=load(P/'formal/audit/original-theta-independent-final-binding-evidence.json')
for name,h in old['all_formal_source_sha256'].items():assert sha(P/'formal'/name)==h,name
pack=load(P/'formal/audit/package-validation.json')
assert sha(P/'deliverables/Lean形式化材料_2026-10-26.zip')==pack['sha256']
for name,h in {'DirectedNetworkComparison':'e1eb401a053c70e20a295f1cf0d22ced4e1b3b7a5ec52b4714d87a7c87a1182a',
               'FullBlockThreshold':'1910b52305e593410d0c190f17e2fafa9f47cfb24acf9b08ad45bce2aeec8d79'}.items():
    assert sha(P/'research/exploration/lean'/f'{name}.lean')==h
sources=[('ImprovedOriginalLower','improved-original-lower-validation.json','improved-original-lower-kernel.log','improved-lower-source-review.json'),
         ('ParameterCounterexample','parameter-counterexample-validation.json',None,'parameter-counterexample-source-review.json'),
         ('RobustNetworkBounds','RobustNetworkBounds-final-cache.json','RobustNetworkBounds-final-cache.log','robust-network-source-review.json'),
         ('RobustTankCertificate','RobustTankCertificate-final.json','RobustTankCertificate-final.log','robust-tank-source-review.json')]
records={};total_named=0;total_theorems=0
for name,meta_name,log_name,review_name in sources:
    src=R/'lean'/f'{name}.lean';meta=load(R/'evidence'/meta_name)
    assert meta['exit_code']==0 and meta['trust_level']==0 and meta['checks_passed']
    assert '--trust=0' in meta['command']
    assert sha(src)==meta['source_sha256']
    if log_name is None:log_name=Path(meta['log_path']).name
    log=R/'evidence'/log_name
    assert sha(log)==meta['log_sha256']
    s=src.read_text(encoding='utf-8');t=log.read_text(encoding='utf-8')
    ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
    expected=[x if '.' in x else ns+'.'+x for x in re.findall(r'^#print axioms (\S+)',s,re.M)]
    actual=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",t)
    assert expected==actual,name
    assert not re.search(r'\berror:|sorryAx',t)
    for entry in re.findall(r'depends on axioms:\s*\[([^]]*)\]',t,re.S):
        assert {x.strip() for x in entry.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
    code=re.sub(r'/-.*?-/', '',s,flags=re.S);code=re.sub(r'--[^\n]*','',code)
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe|constant)\b',code,re.M)
    review=R/'notes'/review_name
    assert meta['source_sha256'] in review.read_text(encoding='utf-8').lower()
    records[name]={'source_sha256':sha(src),'log_sha256':sha(log),'record_sha256':sha(R/'evidence'/meta_name),
                   'review_sha256':sha(review),'named':len(actual),'theorems':len(re.findall(r'^theorem ',s,re.M))}
    total_named+=len(actual);total_theorems+=records[name]['theorems']
bind=load(R/'evidence/improved-original-lower-final-binding.json')
assert bind['full_stage_acceptance'] and bind['kernel_exit_code']==0
reader=load(R/'reader-review.json')
assert reader['status']=='pass' and reader['unresolved_blockers']==[]
for rel,h in reader['reviewed_file_sha256'].items():assert sha(R/rel)==h,rel
fig=load(R/'figure-data.json')
for rel,h in fig['images'].items():assert sha(R/'images'/rel)==h
links=[]
for name in ['README.md','INTERVAL_CERTIFICATE.md']:
    for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',(R/name).read_text(encoding='utf-8')):
        if target.startswith(('http://','https://','#')) or target=='validation.json':continue
        q=R/unquote(target.split('#',1)[0])
        if target.startswith('../'):q=P/'research/exploration/phase2'/unquote(target.split('#',1)[0])
        assert q.resolve().exists(),target
        links.append(target)
for file in R.glob('*.py'):ast.parse(file.read_text(encoding='utf-8'))
artifacts={q.relative_to(R).as_posix():sha(q) for q in sorted(R.rglob('*'))
           if q.is_file() and q.name!='validation.json' and 'build' not in q.relative_to(R).parts}
result={'checked_at':datetime.now().astimezone().isoformat(),'status':'PASS','named_declarations':total_named,
        'new_theorems':total_theorems,'modules':records,'reader_review':reader,'local_links_checked':len(links),
        'original_formal_sources_unchanged':len(old['all_formal_source_sha256']),
        'phase1_math_sources_unchanged':True,'sealed_zip_sha256':pack['sha256'],'artifact_sha256':artifacts,
        'claims':{'new_original_lower_denominator':576000000,'new_original_lower_threshold':500001,
                  'upper_constant_unchanged':664066,'parameter_endpoints_can_miss_interior':True,
                  'five_percent_ode_coefficient_robust_bound':'28077/109744 at (20/19)log2',
                  'new_field_or_global_novelty_certified':False,'actual_human_test':False}}
(R/'validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:result[k] for k in ['status','named_declarations','new_theorems','original_formal_sources_unchanged','local_links_checked']}))
