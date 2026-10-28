"""Read-only mathematical-source checks and local artifact manifest.
Does not rebuild Lean; checks actual separately saved trust=0 runs and readers.
"""
from pathlib import Path
from datetime import datetime
from fractions import Fraction
from urllib.parse import unquote
import hashlib,json,re,ast,argparse

p=argparse.ArgumentParser();p.add_argument('--project',type=Path,required=True)
args=p.parse_args();P=args.project.resolve();R=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
binding=json.loads((P/'formal/audit/original-theta-independent-final-binding-evidence.json').read_text(encoding='utf-8-sig'))
for name,h in binding['all_formal_source_sha256'].items():
    assert sha(P/'formal'/name)==h,name
package=json.loads((P/'formal/audit/package-validation.json').read_text(encoding='utf-8-sig'))
assert sha(P/'deliverables/Lean形式化材料_2026-10-26.zip')==package['sha256']

network=json.loads((R/'evidence/directed-network-final-validation.json').read_text(encoding='utf-8'))
assert network['checks_passed'] and network['exit_code']==0 and network['trust_level']==0
assert sha(R/'lean/DirectedNetworkComparison.lean')==network['source_sha256']
assert sha(R/'evidence/directed-network-final-kernel.log')==network['log_sha256']
assert network['named_declarations']==network['actual_axiom_outputs']
block=json.loads((R/'lean/FullBlockThreshold.validation.json').read_text(encoding='utf-8'))
assert block['exit_code']==0
assert '--trust=0' in block['arguments']
assert sha(R/'lean/FullBlockThreshold.lean')==block['source_sha256']
assert sha(R/'lean/FullBlockThreshold.validation.log')==block['log_sha256']
block_source=(R/'lean/FullBlockThreshold.lean').read_text(encoding='utf-8')
block_expected=[x if '.' in x else 'MathResearchExploration.FullBlockThreshold.'+x
                for x in re.findall(r'^#print axioms (\S+)$',block_source,re.M)]
block_actual=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",
                       (R/'lean/FullBlockThreshold.validation.log').read_text(encoding='utf-8'))
assert block_expected==block_actual
assert len(block_actual)==block['declaration_count']

for source,log in [(R/'lean/DirectedNetworkComparison.lean',R/'evidence/directed-network-final-kernel.log'),
                   (R/'lean/FullBlockThreshold.lean',R/'lean/FullBlockThreshold.validation.log')]:
    s=source.read_text(encoding='utf-8');t=log.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b',s)
    assert not re.search(r'^\s*(axiom|constant|unsafe)\b',s,re.M)
    assert not re.search(r'\berror:|sorryAx',t)
    for entry in re.findall(r'depends on axioms:\s*\[([^]]*)\]',t,re.S):
        assert {x.strip() for x in entry.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}

reader=json.loads((R/'reader-review.json').read_text(encoding='utf-8'))
assert reader['status']=='pass' and reader['unresolved_blockers']==[]
for name,h in reader['reviewed_file_sha256'].items(): assert sha(R/name)==h,name
required={'README.md','NETWORK_PROOF.md','images/three-tanks.png','images/outlet-envelope.png'}
assert required <= set(reader['reviewed_file_sha256'])

links=[]
for doc in [R/'README.md',R/'NETWORK_PROOF.md']:
    for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',doc.read_text(encoding='utf-8')):
        if target.startswith(('https://','http://','#')):continue
        rel=unquote(target.split('#',1)[0])
        if rel=='validation.json':continue
        q=doc.parent/rel
        if rel.startswith('../'):q=P/'research/exploration'/rel
        assert q.resolve().exists(),target
        links.append(target)
for py in R.glob('*.py'):ast.parse(py.read_text(encoding='utf-8'))
data=json.loads((R/'tank-data.json').read_text(encoding='utf-8'))
assert data['numerics']['max_unit_step_analytic_error']<1e-8
for name,h in data['image_sha256'].items():assert sha(R/'images'/name)==h
assert Fraction(19,96)<Fraction(1,5)
artifacts={q.relative_to(R).as_posix():sha(q) for q in sorted(R.rglob('*'))
           if q.is_file() and q.name!='validation.json'}
result={'checked_at':datetime.now().astimezone().isoformat(),'status':'PASS',
        'scope':'two standalone new Lean modules, separately saved trust0 runs; no rebuilt or altered original theorem',
        'original_formal_sources_unchanged':len(binding['all_formal_source_sha256']),
        'sealed_zip_sha256':package['sha256'],
        'network_named':len(network['actual_axiom_outputs']),
        'block_named':block['declaration_count'],
        'network_source_sha256':network['source_sha256'],'block_source_sha256':block['source_sha256'],
        'reader_review':reader,'local_links_checked':len(links),'artifact_sha256':artifacts,
        'new_field_claim':False,'actual_human_test':False,
        'remaining':['propagate improved physical-time bound through synchronous and exact-N conversions',
                     'formally certify coefficient/input uncertainty envelopes beyond fixed network',
                     'whole-theorem tutorial still incomplete']}
(R/'validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k in ['status','network_named','block_named','original_formal_sources_unchanged','local_links_checked']},ensure_ascii=True))
