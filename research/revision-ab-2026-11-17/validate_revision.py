"""Bind final real proof runs, frozen inputs, manuscript, and independent review."""
from pathlib import Path
import hashlib,json,re,sys
from urllib.parse import unquote
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent;P=Path('D:/MyWorks/Math')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
base=load(R/'evidence/base-replay/replay.json');new=load(R/'evidence/unified-build.json')
assert base['status']==new['status']=='PASS'
assert len(base['modules'])==base['source_count']==267
assert new['new_named_declarations']==58 and new['aggregate_axiom_outputs']==105
assert sha(R/'evidence/base-replay/replay.json')==new['fresh_project_replay_sha256']
for rel,h in base['frozen_source_sha256'].items():assert sha(P/'formal'/rel)==h,rel
for name,entry in base['modules'].items():
    tag='analysis' if name.startswith('MathResearchAnalysis') else 'core'
    assert entry['exit_code']==0 and '--trust=0' in entry['command']
    assert sha(Path(entry['command'][-1]))==entry['source_sha256']
    assert sha(Path(entry['command'][entry['command'].index('-o')+1]))==entry['olean_sha256']
    assert sha(R/'evidence/base-replay'/(tag+'-'+name+'.log'))==entry['log_sha256']
for tag in ['core','analysis']:
    entry=base[tag+'_audit'];text=(R/'evidence/base-replay'/(tag+'-fresh-axioms.log')).read_text(encoding='utf-8')
    assert sha(R/'evidence/base-replay'/(tag+'-fresh-axioms.log'))==entry['log_sha256']
    names=re.findall(r"^'(.+)' (?:depends on axioms:|does not depend on any axioms)",text,re.M)
    assert len(names)==entry['declarations']
    assert 'sorryAx' not in text and 'error:' not in text
    for x in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S):
        assert {t.strip() for t in x.split(',') if t.strip()}<={'propext','Classical.choice','Quot.sound'}
for entry in new['modules']+[new['aggregate']]:
    assert entry['exit_code']==0 and entry['trust_level']==0 and entry['fresh_project_base']
    assert sha(Path(entry['source']))==entry['source_sha256']
    assert sha(Path(entry['olean']))==entry['olean_sha256']
    assert sha(R/'evidence'/(entry['module']+'.log'))==entry['log_sha256']
frozen_paper={
 'paper.md':'2b3411cb3c8f661650b3f1e7390d58aa8d91db10ec2ef75e0e8d9ab8361b59d0',
 'tex/main.tex':'e452ef700a34bde8da641cd4a684599e345296e9e31b04f20320a7ceada8195c',
 'output/pdf/quadratic-recovery-working-draft-v5.pdf':'af2c00a836d9ffb29ad05c2e3e2e98619dcc421c67e8c038933fb957cef7adc1'}
for rel,h in frozen_paper.items():assert sha(P/'research/manuscript/quadratic-recovery-v5'/rel)==h
pack=load(P/'formal/audit/package-validation.json')
assert sha(P/'deliverables/Lean形式化材料_2026-10-26.zip')==pack['sha256']
review=load(R/'evidence/independent-source-review.json')
assert review['paper']['sha256']==sha(R/'paper/paper.md')
for m in review['modules']:assert sha(R/m['source'])==m['source_sha256']
final_review=load(R/'evidence/independent-final-binding.json')
assert final_review['status']=='PASS'
assert final_review['unified_build_sha256']==sha(R/'evidence/unified-build.json')
assert final_review['base_replay_sha256']==sha(R/'evidence/base-replay/replay.json')
pdf=load(R/'paper/review/pdf-validation.json')
assert pdf['status']=='PASS' and pdf['all_pages_rendered'] and pdf['all_pages_visually_inspected']
assert pdf['paper_sha256']==sha(R/'paper/paper.md')
assert pdf['pdf_sha256']==sha(R/'paper/output/pdf/quadratic-recovery-v6.pdf')
assert len(pdf['page_images'])==pdf['pages']
for rel,h in pdf['page_images'].items():assert sha(R/'paper'/rel)==h
for rel,h in pdf['contact_sheets_inspected'].items():assert sha(R/'paper'/rel)==h
s=(R/'paper/paper.md').read_text(encoding='utf-8')
tags=re.findall(r'\\tag\{([^}]+)\}',s);assert len(tags)==len(set(tags))
assert len(re.findall(r'!\[[^\]]*\]\(',s))==6
for t in ['576000000','500001','664066','331776','332033','\\tag{4b}','\\tag{4e}']:assert t in s
assert 'This manuscript task has not rerun' not in s
links=[]
for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',s):
    if target.startswith(('https://','http://','#')):continue
    rel=unquote(target.split('#',1)[0]);q=(R/'paper'/rel).resolve()
    if q.exists():links.append({'target':target,'resolved':str(q)});continue
    q=(P/'research/revision-ab-2026-11-17/paper'/rel).resolve()
    if target=='../validation.json':continue
    assert q.exists(),target
    links.append({'target':target,'resolved':str(q)})
result={'status':'PASS','tasks_completed':['A1','A2','A3','B1','B2','B3'],
 'tasks_reserved_for_collaborators':['C1','C2'],'reader_acceptance':'waived by explicit user instruction 2026-11-17',
 'fresh_project_sources':267,'fresh_analysis_sources':259,'fresh_core_sources':8,
 'external_dependencies_reused':'locked Lean and mathlib; these external libraries were not rebuilt',
 'base_axiom_outputs':base['analysis_audit']['declarations']+base['core_audit']['declarations'],
 'new_modules':5,'new_named_declarations':58,'new_theorems':52,'new_definitions':6,
 'copied_existing_modules':2,'existing_dependency_declarations':47,'aggregate_axiom_outputs':105,
 'standard_lean_trust':0,'allowed_axioms':['propext','Classical.choice','Quot.sound'],
 'frozen_sources_unchanged':267,'frozen_paper_unchanged':frozen_paper,'frozen_zip_unchanged':pack['sha256'],
 'paper_sha256':sha(R/'paper/paper.md'),'pdf_sha256':pdf['pdf_sha256'],'pdf_pages':pdf['pages'],
 'paper_equation_tags':len(tags),'local_links_checked':len(links)+1,'local_link_resolutions':links,
 'source_sha256':{p.relative_to(R).as_posix():sha(p) for p in sorted((R/'lean').rglob('*.lean'))},
 'evidence_sha256':{str(p.relative_to(R)):sha(p) for p in [R/'evidence/base-replay/replay.json',R/'evidence/unified-build.json',R/'evidence/independent-source-review.json',R/'evidence/independent-final-binding.json',R/'paper/review/pdf-validation.json']},
 'not_certified':['human expert refereeing','global novelty or priority','arXiv submission readiness'],
 'external_publication':False}
(R/'validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:result[k] for k in ['status','tasks_completed','fresh_project_sources','new_named_declarations','aggregate_axiom_outputs','pdf_pages']},ensure_ascii=False))
