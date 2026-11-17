"""Rerun axiom output after fixing apostrophe-containing Lean-name parsing."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent;P=Path('D:/MyWorks/Math');F=P/'formal';out=R/'evidence/base-replay'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((out/'replay.json').read_text(encoding='utf-8'))
assert len(b['modules'])==b['source_count']==267
for name,e in b['modules'].items():
    assert e['exit_code']==0 and sha(Path(e['command'][-1]))==e['source_sha256']
    assert sha(Path(e['command'][e['command'].index('-o')+1]))==e['olean_sha256']
for rel,h in b['frozen_source_sha256'].items():assert sha(F/rel)==h
prior={'failed_record_sha256':sha(out/'replay.json'),'reason':'Postprocessor used a regex that excluded apostrophes in Lean declaration names; all 267 source compilations and the Lean audit itself succeeded. No mathematical source or kernel setting was changed.'}
(out/'parser-correction.json').write_text(json.dumps(prior,indent=2)+'\n',encoding='utf-8')
b['status']='running corrected audit';b.pop('error',None)
(out/'replay.json').write_text(json.dumps(b,indent=2)+'\n',encoding='utf-8')
for tag,project,version in [('core',F,'4.35.0'),('analysis',F/'analysis','4.35.0-rc4')]:
    cache=R/'fresh-base'/tag;paths=[cache]
    if tag=='analysis':paths += [p/'.lake/build/lib/lean' for p in (project/'.lake/packages').iterdir() if p.is_dir()]
    env=os.environ.copy();env['LEAN_PATH']=';'.join(map(str,paths))
    src=R/(tag+'-fresh-axioms.lean');log=out/(tag+'-fresh-axioms.log')
    cmd=[str(F/('.tools/lean-'+version+'-windows/bin/lean.exe')),'--trust=0',str(src)]
    with log.open('w',encoding='utf-8') as f:run=subprocess.run(cmd,cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text(encoding='utf-8');names=re.findall(r"^'(.+)' (?:depends on axioms:|does not depend on any axioms)",text,re.M)
    expected=re.findall(r'^#print axioms (\S+)',src.read_text(encoding='utf-8'),re.M)
    assert run.returncode==0 and names==expected,(tag,run.returncode,len(names),len(expected))
    assert 'sorryAx' not in text and 'error:' not in text
    for item in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S):
        assert {x.strip() for x in item.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
    b[tag+'_audit']={'command':cmd,'exit_code':0,'declarations':len(names),'log_sha256':sha(log),'audit_source_sha256':sha(src),'cache':str(cache)}
    print(tag,len(names),'axiom outputs PASS',flush=True)
b['status']='PASS';b['frozen_sources_unchanged']=True;b['finished']=time.time();b['parser_correction']=prior
(out/'replay.json').write_text(json.dumps(b,indent=2)+'\n',encoding='utf-8')
print('Fresh 267-source replay and both axiom audits PASS',flush=True)
