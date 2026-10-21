"""Build and audit every named public declaration in the full actual residual waiting and next-mark product law independent of the stopped past."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
from datetime import datetime,timezone,timedelta
sys.stdout.reconfigure(encoding="utf8")
formal=Path(__file__).resolve().parents[1]
project=formal/"analysis"
binpath=formal/".tools/lean-4.35.0-rc4-windows/bin"
audit=formal/"audit"
modules=sys.argv[1:]
assert modules and all(re.fullmatch(r"[A-Za-z0-9_]+",m) for m in modules)
env=os.environ.copy()
env["PATH"]=str(binpath)+os.pathsep+env.get("PATH","")
hashes={}
names=[]
for mod in modules:
    p=project/"MathResearchAnalysis"/(mod+".lean")
    s=p.read_text(encoding="utf8")
    ns=re.search(r"^namespace (\S+)",s,re.M).group(1)
    names.extend(ns+"."+m.group(1) for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|abbrev|instance)\s+(\S+)",s,re.M))
    hashes[p.relative_to(project).as_posix()]=hashlib.sha256(p.read_bytes()).hexdigest()
assert names and len(names)==len(set(names))
source=audit/"marked-residual-pair-stage-declarations-axioms.lean"
source.write_text("\n".join("import MathResearchAnalysis."+m for m in modules)+"\n\n"+"\n".join("#print axioms "+n for n in names)+"\n",encoding="utf8")
def run(args,name):
    r=subprocess.run([str(binpath/"lake.exe"),*args],cwd=project,env=env,capture_output=True,text=True,encoding="utf8",errors="replace")
    (audit/name).write_text(r.stdout+r.stderr+f"\nEXIT_CODE={r.returncode}\n",encoding="utf8")
    assert r.returncode==0,(name,r.stdout[-5000:],r.stderr[-2000:])
    return r.stdout+r.stderr
build=run(["build",*("MathResearchAnalysis."+m for m in modules)],"marked-residual-pair-stage-declarations-build.log")
out=run(["env","lean","--trust=0",str(source)],"marked-residual-pair-stage-declarations-axioms.log")
assert "sorryAx" not in out and "error:" not in out
for n in names:
    assert f"'{n}' depends on axioms:" in out or f"'{n}' does not depend on any axioms" in out,n
axioms={x.strip() for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out) for x in body.split(",") if x.strip()}
assert axioms<={"Classical.choice","propext","Quot.sound"},axioms
for name,sha in hashes.items(): assert hashlib.sha256((project/name).read_bytes()).hexdigest()==sha
record={"validated_at":datetime.now(timezone(timedelta(hours=8))).isoformat(),"modules":modules,"named_declarations":names,"declarations_count":len(names),"build_exit":0,"axiom_audit_exit":0,"kernel_trust_level":0,"axioms_seen":sorted(axioms),"source_sha256":hashes,"new_lean_warning_lines":[line for line in build.splitlines() if "warning:" in line and "batteries:" not in line]}
(audit/"marked-residual-pair-stage-declarations-validation.json").write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding="utf8")
print(json.dumps({k:v for k,v in record.items() if k not in {"named_declarations","source_sha256"}},ensure_ascii=False))
