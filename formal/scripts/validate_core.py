"""Rebuild and audit the actual Lean project, excluding third-party snapshots."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys
from datetime import datetime, timezone, timedelta

sys.stdout.reconfigure(encoding='utf8')

ROOT=Path(__file__).resolve().parents[1]
BIN=ROOT/'.tools'/'lean-4.35.0-windows'/'bin'
env=os.environ.copy()
env['PATH']=str(BIN)+os.pathsep+env.get('PATH','')
audit=ROOT/'audit'; audit.mkdir(exist_ok=True)

def without_comments(source):
    out=[]; i=0; depth=0
    while i<len(source):
        if source.startswith('/-',i): depth+=1; out.extend('  '); i+=2
        elif depth and source.startswith('-/',i): depth-=1; out.extend('  '); i+=2
        elif depth: out.append('\n' if source[i]=='\n' else ' '); i+=1
        elif source.startswith('--',i):
            end=source.find('\n',i)
            if end<0: end=len(source)
            out.extend(' '*(end-i)); i=end
        else: out.append(source[i]); i+=1
    return ''.join(out)

files=sorted((ROOT/'MathResearch').glob('*.lean'))+[ROOT/'MathResearch.lean']
declarations=[]; source_hashes={}
for path in files:
    raw=path.read_text(encoding='utf8'); code=without_comments(raw)
    source_hashes[path.relative_to(ROOT).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code)
    if forbidden: raise RuntimeError(f'Forbidden proof construct in {path.name}: {forbidden}')
    if 'debug.skipKernelTC' in code: raise RuntimeError('Kernel checking disabled')
    scopes=[]; prefix=[]
    for line in code.splitlines():
        stripped=line.strip()
        match=re.match(r'namespace\s+(\S+)',stripped)
        if match:
            names=match.group(1).split('.')
            scopes.append(('namespace',len(names)))
            prefix+=names
            continue
        if re.match(r'section(?:\s|$)',stripped): scopes.append(('section',0)); continue
        if re.match(r'end(?:\s|$)',stripped):
            if scopes:
                kind,n=scopes.pop()
                if n: prefix=prefix[:-n]
            continue
        match=re.match(r'(?:@\[[^\]]*\]\s*)?theorem\s+(\S+)',stripped)
        if match: declarations.append('.'.join(prefix+[match.group(1)]))
declarations+=['MathResearch.Grid.system']
assert len(declarations)==len(set(declarations))
axiom_source='import MathResearch\n\n'+'\n'.join(f'#print axioms {name}' for name in declarations)+'\n'
(audit/'CoreAxioms.lean').write_text(axiom_source,encoding='utf8')

def run(args, filename):
    proc=subprocess.run([str(BIN/'lake.exe'),*args],cwd=ROOT,env=env,
                        capture_output=True,text=True,encoding='utf8',errors='replace')
    output=proc.stdout+proc.stderr
    (audit/filename).write_text(output+f'\nEXIT_CODE={proc.returncode}\n',encoding='utf8')
    print(output,end='')
    if proc.returncode: raise RuntimeError(f'{args} failed with exit {proc.returncode}')
    return output

compiler=subprocess.run([str(BIN/'lean.exe'),'--version'],env=env,
                        capture_output=True,text=True,encoding='utf8',check=True).stdout.strip()
if 'version 4.35.0,' not in compiler: raise RuntimeError(f'Wrong core compiler: {compiler}')
build=run(['build'],'core-build.log')
axioms=run(['env','lean','--trust=0','audit/CoreAxioms.lean'],'core-axioms.log')
if 'sorryAx' in axioms or 'error:' in axioms: raise RuntimeError('Axiom audit failed')
allowed={'propext','Classical.choice','Quot.sound'}
dependencies=[]
for body in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',axioms):
    dependencies += [part.strip() for part in body.split(',') if part.strip()]
unexpected=set(dependencies)-allowed
if unexpected: raise RuntimeError(f'Unexpected axioms: {sorted(unexpected)}')
for name in declarations:
    if f"'{name}' depends on axioms:" not in axioms and \
            f"'{name}' does not depend on any axioms" not in axioms:
        raise RuntimeError(f'Missing axiom output for {name}')
summary={'compiler':'Lean 4.35.0','public_theorems':len(declarations)-1,
         'validated_at':datetime.now(timezone(timedelta(hours=8))).isoformat(),
         'compiler_output':compiler,
         'additional_model_definitions':1,'project_lean_files':len(files),
         'build_exit':0,'axiom_audit_exit':0,
         'kernel_trust_level':0,
         'axiom_audit_command':'lake env lean --trust=0 audit/CoreAxioms.lean',
         'axioms_seen':sorted(set(dependencies)),
         'custom_axioms':False,'admitted_holes':False,
         'source_sha256':source_hashes,
         'scope':'deterministic components, not the full quadratic probability theorem'}
(audit/'core-validation.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({k:v for k,v in summary.items() if k!='source_sha256'},ensure_ascii=False))
