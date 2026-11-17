from pathlib import Path
import hashlib,json,zipfile
R=Path(__file__).resolve().parent
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
assert load(R/'validation.json')['status']=='PASS'
assert load(R/'evidence/independent-final-binding.json')['status']=='PASS'
exclude={'fresh-base','build','final-build','__pycache__','rendered','rendered-final','tex-build'}
files={}
for p in sorted(R.rglob('*')):
    rel=p.relative_to(R)
    if not p.is_file() or any(x in exclude for x in rel.parts) or p.suffix=='.zip' or p.name in {'MANIFEST.json','PACKAGE.json','PERSISTENCE.json'}:continue
    files[rel.as_posix()]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(R/'MANIFEST.json').write_text(json.dumps({'archive_root':'research/revision-ab-2026-11-17','files':files,'compiled_caches_included':False,'rendered_page_pngs_included':False},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
archive=R/'A1-A3_B1-B3_2026-11-17.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=8) as z:
    for rel in list(files)+['MANIFEST.json']:z.write(R/rel,'research/revision-ab-2026-11-17/'+rel)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for rel,item in files.items():assert hashlib.sha256(z.read('research/revision-ab-2026-11-17/'+rel)).hexdigest()==item['sha256']
result={'status':'PASS','zip':archive.name,'zip_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'bytes':archive.stat().st_size,'files':len(files)+1,'external_publication':False,'cache_location':'C staging; fresh artifact SHA256 recorded in build evidence'}
(R/'PACKAGE.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False))
