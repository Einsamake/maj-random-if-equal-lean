"""Publish an exact-byte, reviewed documentation snapshot; no commit or push."""
from pathlib import Path
import ast,hashlib,json,re,subprocess
from urllib.parse import unquote
P=Path('D:/MyWorks/Math'); T=P/'repository/maj-random-if-equal-lean'; R=P/'docs/revision-2026-10-28'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
reader=load(R/'reader-final-reread.json')
assert reader['status']=='pass' and reader['unresolved_blockers']==[]
for rel,h in reader['reviewed_file_sha256'].items():assert sha(P/rel)==h.lower(),rel
base=load(P/'formal/audit/original-theta-independent-final-binding-evidence.json')
for rel,h in base['all_formal_source_sha256'].items():
    assert sha(P/'formal'/rel)==h,rel
    assert sha(T/'formal'/rel)==h,('repository formal',rel)
F=P/'research/exploration'
tracked=set(subprocess.check_output(['git','ls-files'],cwd=T,text=True,encoding='utf-8').splitlines())
frozen_count=0
for q in F.rglob('*freeze*.json'):
    for rel,h in load(q).items():
        assert isinstance(h,str) and re.fullmatch('[0-9a-fA-F]{64}',h),(q,rel)
        assert sha(F/rel)==h,(q,rel)
        frozen_count+=1
assert sha(P/'deliverables/Lean形式化材料_2026-10-26.zip')=='16f7715e4f2d4a98a6b30a3ab6a6471ea9063de93c9588acf84a2e9d8a280892'
selected={Path(x) for x in ['README.md','STATUS.md','docs/RESEARCH_RESULTS.md']}
root_explore=['README.md','phase1-overview.md','NETWORK_PROOF.md','reader-review.json','render_tanks.py','tank-data.json','validate_exploration.py','validation.json']
selected.update(Path('research/exploration')/n for n in root_explore)
exclude_parts={'build','__pycache__','.lake','.tools','.git'}
exclude_names={'RUN_STATE.json','CHECKPOINT.md','resume-state.json','next-stage-plan.json'}
for sub in ['images','lean','evidence']+[f'phase{i}' for i in range(2,13)]:
    for p in (F/sub).rglob('*'):
        if p.is_file() and not (set(p.relative_to(F).parts)&exclude_parts) and p.name not in exclude_names:
            selected.add(p.relative_to(P))
for n in ['phase10-freeze.json','phase12-freeze.json']:
    selected.add(Path('research/exploration/notes')/n)
for p in (P/'docs/proof-discovery').rglob('*'):
    if p.is_file() and not (set(p.relative_to(P).parts)&exclude_parts) and p.suffix not in {'.olean','.ilean','.pyc'}:
        selected.add(p.relative_to(P))
# The public snapshot omits generated caches and scheduler state. Evidence remains byte-identical.
for n in ['terra-editing-record.json','reader-first-feedback.json','reader-final-reread.json','scientific-factcheck.json']:
    selected.add(Path('docs/revision-2026-10-28')/n)
selected.add(Path('docs/revision-2026-10-28/publish_reviewed_docs.py'))
selected.update(Path('deliverables')/n for n in ['README.md','Lean形式化材料_2026-10-26.zip','Lean形式化材料_2026-10-26.zip.sha256'])
while True:
    additions=set()
    for rel in selected:
        if rel.suffix!='.md':continue
        body=(P/rel).read_text(encoding='utf-8-sig')
        body=re.sub(r'\$\$[\s\S]*?\$\$|\$[^$\n]*\$', '',body)
        for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',body):
            target=target.strip('<>').split('#')[0]
            if not target or '://' in target or re.match(r'^[A-Za-z]:',target):continue
            target=re.sub(r':\d+$','',unquote(target)); q=(P/rel.parent/target).resolve()
            if not q.is_relative_to(P.resolve()) or not q.is_file():continue
            qr=q.relative_to(P)
            if qr.as_posix() in tracked or qr in selected:continue
            assert not (set(qr.parts)&exclude_parts) and q.name not in exclude_names,qr
            additions.add(qr)
    if not additions:break
    selected.update(additions)
secret=re.compile(r'(?:gh[pousr]_[A-Za-z0-9_]{25,}|sk-[A-Za-z0-9_-]{24,}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----)')
for rel in sorted(selected):
    p=P/rel; assert p.is_file(),rel
    raw=p.read_bytes()
    if p.suffix not in {'.png','.gif','.jpg','.jpeg','.zip'}:
        s=raw.decode('utf-8-sig'); assert not secret.search(s),rel
    out=T/rel; assert out.resolve().is_relative_to(T.resolve())
    out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
links=0; checked=[]
for rel in sorted(selected):
    p=T/rel
    if p.suffix!='.md' or set(rel.parts)&{'notes','reviews'}:continue
    s=p.read_text(encoding='utf-8-sig')
    s=re.sub(r'\$\$[\s\S]*?\$\$|\$[^$\n]*\$', '',s)
    for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',s):
        target=target.strip('<>').split('#')[0]
        if not target or target.startswith(('https://','http://','mailto:')):continue
        target=re.sub(r':\d+$','',unquote(target)); q=(p.parent/target).resolve()
        assert q.is_relative_to(T.resolve()) and q.exists(),(str(rel),target)
        links+=1
    checked.append(rel.as_posix())
for n in ['README.md','STATUS.md','docs/RESEARCH_RESULTS.md','research/exploration/README.md']:
    assert sha(P/n)==sha(T/n)
reader=load(R/'reader-final-reread.json')
assert reader['status']=='pass' and reader['unresolved_blockers']==[]
for rel,h in reader['reviewed_file_sha256'].items():assert sha(P/rel)==h.lower(),rel
manifest=load(T/'SNAPSHOT_MANIFEST.json')
for rel in sorted(selected):
    p=T/rel; original=P/rel
    manifest['files'][rel.as_posix()]={'bytes':p.stat().st_size,'sha256':sha(p),'workspace_sha256':sha(original),'byte_identical_to_workspace':True}
manifest['documentation_update']={'date':'2026-10-28','writer_model':'gpt-6.1-terra','latest_complete_research_stage':'phase12','scope':'Scholar-facing documentation plus exact-byte accepted exploration and tutorial support. No new mathematical proof or original-source rebuild in this update.','evidence_note':'New exploration/tutor evidence bytes are unchanged. Generated Lean caches are omitted; recorded cache fingerprints refer to the accepted local builds. Historical root evidence retains prior snapshot sanitization as noted above.','selected_files':len(selected),'local_links_checked':links}
(T/'SNAPSHOT_MANIFEST.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
record={'status':'PASS','selected_files':len(selected),'local_links_checked':links,'markdown_files_checked':checked,'historical_draft_link_scope':'Immutable archived notes/reviews retain their original source-relative links; only active reader-facing documents are link-checked.','frozen_fingerprint_checks':frozen_count,'original_formal_sources_unchanged':len(base['all_formal_source_sha256']),'proof_rebuilt_in_this_documentation_update':False,'published_selection_sha256':{p.as_posix():sha(T/p) for p in sorted(selected)},'snapshot_manifest_sha256':sha(T/'SNAPSHOT_MANIFEST.json')}
(R/'publication-preflight.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['published_selection_sha256','markdown_files_checked']},ensure_ascii=False))
