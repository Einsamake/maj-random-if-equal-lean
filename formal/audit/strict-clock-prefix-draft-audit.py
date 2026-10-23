from pathlib import Path
import hashlib,json,os,re,subprocess,sys
from datetime import datetime,timezone,timedelta
sys.stdout.reconfigure(encoding="utf8")
formal=Path(r"D:\MyWorks\Math\formal")
project=formal/"analysis"
binpath=formal/".tools/lean-4.35.0-rc4-windows/bin"
audit=formal/"audit"
source=formal/"drafts/StrictClockPrefix.lean"
s=source.read_text(encoding="utf8")
sha=hashlib.sha256(source.read_bytes()).hexdigest()
ns=re.search(r"^namespace (\S+)",s,re.M).group(1)
names=[ns+"."+m.group(1) for m in re.finditer(r"^(?:theorem|lemma|def|abbrev|instance)\s+(\S+)",s,re.M)]
assert names and len(names)==len(set(names))
env=os.environ.copy()
env["PATH"]=str(binpath)+os.pathsep+env.get("PATH","")
combined=audit/"strict-clock-prefix-draft-named.lean"
combined.write_text(s+"\n"+"\n".join("#print axioms "+n for n in names)+"\n",encoding="utf8")
r=subprocess.run([str(binpath/"lake.exe"),"env","lean","--trust=0",str(combined)],cwd=project,env=env,capture_output=True,text=True,encoding="utf8",errors="replace")
out=r.stdout+r.stderr
(audit/"strict-clock-prefix-draft-named.log").write_text(out+f"\nEXIT_CODE={r.returncode}\n",encoding="utf8")
assert r.returncode==0,(r.returncode,out[-10000:])
assert "sorryAx" not in out and "error:" not in out
for n in names:
    assert f"'{n}' depends on axioms:" in out or f"'{n}' does not depend on any axioms" in out,n
axioms={x.strip() for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out) for x in body.split(",") if x.strip()}
assert axioms<={"Classical.choice","propext","Quot.sound"},axioms
assert hashlib.sha256(source.read_bytes()).hexdigest()==sha
record={"validated_at":datetime.now(timezone(timedelta(hours=8))).isoformat(),"source":str(source),"source_sha256":sha,"named_declarations":names,"declarations_count":len(names),"kernel_trust_level":0,"exit_code":r.returncode,"axioms_seen":sorted(axioms),"warning_lines":[line for line in out.splitlines() if "warning:" in line and "batteries:" not in line],"proof_boundary":"Deterministic true strict-past words and endpoint event identity; no predictable-state or actual Dynkin claim."}
(audit/"strict-clock-prefix-draft-validation.json").write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding="utf8")
print(json.dumps(record,ensure_ascii=False,indent=2))
