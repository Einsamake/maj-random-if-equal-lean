"""Fresh project-source replay; mathlib/Lean remain the locked installed dependencies."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib,json,os,re,subprocess,sys,time
sys.stdout.reconfigure(encoding='utf-8')
R=Path(__file__).resolve().parent; P=Path('D:/MyWorks/Math'); F=P/'formal'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
frozen=json.loads((F/'audit/original-theta-independent-final-binding-evidence.json').read_text(encoding='utf-8-sig'))['all_formal_source_sha256']
assert all(sha(F/q)==h for q,h in frozen.items()),'Frozen formal source changed before replay'
record={'status':'running','started':time.time(),'source_count':len(frozen),'modules':{},'frozen_source_sha256':frozen,'dependency_scope':'Fresh project sources. Installed locked Lean and mathlib dependencies reused, not rebuilt.'}
out=R/'evidence/base-replay';out.mkdir(parents=True,exist_ok=True)
def save(): (out/'replay.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
def run_project(project, sources, tag, binary, audit_source):
    cache=R/'fresh-base'/tag;cache.mkdir(parents=True,exist_ok=True)
    paths=[cache]
    if tag=='analysis':paths += [q/'.lake/build/lib/lean' for q in (project/'.lake/packages').iterdir() if q.is_dir()]
    env=os.environ.copy();env['LEAN_PATH']=';'.join(map(str,paths))
    modules={q.relative_to(project).with_suffix('').as_posix().replace('/','.'):q for q in sources}
    deps={m:{i for i in re.findall(r'^\s*(?:public )?import\s+([\w.]+)',q.read_text(encoding='utf-8'),re.M) if i in modules} for m,q in modules.items()}
    done=set();running={}
    def compile_one(m,q):
        target=cache/(m.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        log=out/(tag+'-'+m+'.log');cmd=[str(binary),'--trust=0','--root='+str(project),'-o',str(target),str(q)]
        t=time.time()
        with log.open('w',encoding='utf-8') as f:r=subprocess.run(cmd,cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
        return {'exit_code':r.returncode,'seconds':time.time()-t,'command':cmd,'source_sha256':sha(q),'log_sha256':sha(log),'olean_sha256':sha(target) if target.exists() else None}
    with ThreadPoolExecutor(max_workers=2) as pool:
        while len(done)<len(modules):
            for m in sorted(set(modules)-done-set(running.values())):
                if len(running)>=2:break
                if deps[m]<=done:running[pool.submit(compile_one,m,modules[m])]=m
            if not running:raise RuntimeError('Source dependency cycle: '+str(set(modules)-done))
            finished,_=wait(running,return_when=FIRST_COMPLETED)
            for future in finished:
                m=running.pop(future);item=future.result();record['modules'][m]=item;save()
                if item['exit_code']:raise RuntimeError(m+' failed; inspect fresh log')
                done.add(m)
                print(tag,len(done),'/',len(modules),m,round(item['seconds'],1),flush=True)
    audit=R/(tag+'-fresh-axioms.lean');audit.write_bytes(audit_source.read_bytes())
    log=out/(tag+'-fresh-axioms.log');cmd=[str(binary),'--trust=0',str(audit)]
    with log.open('w',encoding='utf-8') as f:r=subprocess.run(cmd,cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text(encoding='utf-8');actual=re.findall(r"^'(.+)' (?:depends on axioms:|does not depend on any axioms)",text,re.M)
    expected=re.findall(r'^#print axioms (\S+)',audit.read_text(encoding='utf-8'),re.M)
    axioms=[{s.strip() for s in a.split(',') if s.strip()} for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)]
    assert r.returncode==0 and expected==actual and all(s<={'propext','Classical.choice','Quot.sound'} for s in axioms)
    assert 'sorryAx' not in text and 'error:' not in text
    record[tag+'_audit']={'command':cmd,'exit_code':r.returncode,'declarations':len(actual),'log_sha256':sha(log),'audit_source_sha256':sha(audit),'cache':str(cache)};save()
try:
    run_project(F,[F/q for q in frozen if not q.startswith('analysis/')],'core',F/'.tools/lean-4.35.0-windows/bin/lean.exe',F/'audit/CoreAxioms.lean')
    run_project(F/'analysis',[F/q for q in frozen if q.startswith('analysis/')],'analysis',F/'.tools/lean-4.35.0-rc4-windows/bin/lean.exe',F/'analysis/AnalysisAxioms.lean')
    assert all(sha(F/q)==h for q,h in frozen.items())
    record['status']='PASS';record['frozen_sources_unchanged']=True
except Exception as e:
    record['status']='FAILED';record['error']=str(e);raise
finally:
    record['finished']=time.time();save()
