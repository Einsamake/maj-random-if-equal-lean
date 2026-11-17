"""Persist only this new revision; never replace frozen project artifacts."""
from pathlib import Path
import hashlib,json,shutil,sys
sys.stdout.reconfigure(encoding='utf-8')
S=Path(__file__).resolve().parent; D=Path('D:/MyWorks/Math/research/revision-ab-2026-11-17').resolve()
assert D.parent==Path('D:/MyWorks/Math/research').resolve() and D.name=='revision-ab-2026-11-17'
D.mkdir(parents=True,exist_ok=True)
exclude={'fresh-base','build','final-build','__pycache__','rendered','rendered-final','tex-build'}
copied={}
for p in sorted(S.rglob('*')):
    rel=p.relative_to(S)
    if not p.is_file() or any(x in exclude for x in rel.parts):continue
    q=D/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
    h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
    copied[rel.as_posix()]=h
(D/'PERSISTENCE.json').write_text(json.dumps({'source':str(S),'target':str(D),'files':copied,'compiled_caches':'isolated C staging, artifact hashes in evidence; not copied'},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'files':len(copied),'target':str(D)},ensure_ascii=False))
