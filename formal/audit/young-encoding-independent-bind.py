"""Independent read-only binding of the actual finite Young encoding and bidirectional local-transition audits."""
from pathlib import Path
import re,json,hashlib,sys
from datetime import datetime,timezone,timedelta
sys.stdout.reconfigure(encoding='utf8')
F=Path(__file__).resolve().parents[1]
A=F/'audit'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return p.read_text(encoding='utf-8-sig')
def load(p):return json.loads(read(p))
def strip_comments(s):
    # Independent lexer: preserve newlines and nested-comment structure.
    out=[]; pos=0; depth=0
    while pos<len(s):
        if s[pos:pos+2]=='/-':depth+=1;pos+=2;out.append(' ');continue
        if depth:
            if s[pos:pos+2]=='-/':depth-=1;pos+=2;out.append(' ')
            else:
                if s[pos]=='\n':out.append('\n')
                pos+=1
            continue
        if s[pos:pos+2]=='--':
            nxt=s.find('\n',pos)
            pos=len(s) if nxt<0 else nxt
            continue
        out.append(s[pos]);pos+=1
    assert depth==0
    return ''.join(out)
def source_names(p,kinds=('theorem','lemma')):
    code=strip_comments(read(p))
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code),p
    assert 'debug.skipKernelTC' not in code,p
    scopes=[];prefix=[];out=[]
    for raw in code.splitlines():
        ln=raw.strip()
        ln=re.sub(r'^(?:@\[[^\]]*\]\s*)+','',ln)
        ln=re.sub(r'^(?:(?:public|noncomputable)\s+)+','',ln)
        m=re.match(r'namespace\s+(\S+)',ln)
        if m:
            scopes.append(list(prefix));prefix+=m[1].split('.');continue
        if re.match(r'section(?:\s|$)',ln):scopes.append(list(prefix));continue
        if re.match(r'end(?:\s|$)',ln):
            if scopes:prefix=scopes.pop()
            continue
        m=re.match(r'('+('|'.join(kinds))+r')\s+(\S+)',ln)
        if m:out.append(('.'.join(prefix+[m[2]]),m[1]))
    return out
allowed={'propext','Classical.choice','Quot.sound'}
def actual_names(log):
    txt=read(log)
    assert txt.rstrip().endswith('EXIT_CODE=0'),log
    assert 'sorryAx' not in txt and 'error:' not in txt,log
    rows=list(re.finditer(r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",txt,re.M))
    names=[r[1] for r in rows]
    axs={a.strip() for r in rows if r[2] for a in r[2].split(',') if a.strip()}
    assert names and len(names)==len(set(names)),log
    assert axs<=allowed,(log,axs)
    return names,axs

def bind_group(label,project,folder,entry,record,table,log,build,model=[]):
    d=load(record)
    files=sorted((project/folder).glob('*.lean'))+[project/entry]
    now={p.relative_to(project).as_posix():sha(p) for p in files}
    assert now==d['source_sha256'],label
    assert len(files)==d['project_lean_files'],label
    assert d['build_exit']==d['axiom_audit_exit']==d['kernel_trust_level']==0,label
    assert d['custom_axioms']==d['admitted_holes']==False,label
    assert '--trust=0' in d['axiom_audit_command'],label
    assert read(build).rstrip().endswith('EXIT_CODE=0'),label
    names=[n for p in files for n,k in source_names(p)]+model
    tables=re.findall(r'^#print axioms (\S+)\s*$',read(table),re.M)
    outputs,axs=actual_names(log)
    assert names==tables==outputs,(label,len(names),len(tables),len(outputs))
    assert len(names)==d['public_theorems']+d.get('additional_model_definitions',0)
    assert axs==set(d['axioms_seen'])
    return {'validated_at':d['validated_at'],'sources':len(files),'public_theorems':d['public_theorems'],
      'additional_model_definitions':d.get('additional_model_definitions',0),
      'all_source_set_and_sha_exact':True,'source_declarations_match_actual_output':True,
      'all_printed_names_and_order_exact':True,'count':len(names),
      'names_with_apostrophes':sum("'" in n for n in names),
      'names_order_sha256':hashlib.sha256(('\n'.join(names)+'\n').encode()).hexdigest(),
      'axioms':sorted(axs),'table_sha256':sha(table),'log_sha256':sha(log),'build_log_sha256':sha(build),
      'validation_sha256':sha(record)},now
analysis,anow=bind_group('analysis',F/'analysis','MathResearchAnalysis','MathResearchAnalysis.lean',A/'analysis-validation.json',F/'analysis/AnalysisAxioms.lean',A/'analysis-axioms.log',A/'analysis-build.log')
core,cnow=bind_group('core',F,'MathResearch','MathResearch.lean',A/'core-validation.json',A/'CoreAxioms.lean',A/'core-axioms.log',A/'core-build.log',['MathResearch.Grid.system'])
assert analysis['sources']==222 and core['sources']==8
assert analysis['count']==2956 and core['count']==126
mods=['YoungParticles','YoungRowUpdates','YoungParticleInverse','YoungParticleMoves','YoungParticleHops']
expected_hashes={
 'YoungParticles':'ec769948d2d03100d2337b1c4c2cf44aaeeec7d8f4525cb370def055c793a85b',
 'YoungRowUpdates':'558e07bb40a9b8b11a5b6d880a2836c265baa102656dad41836b61f8facbad80',
 'YoungParticleInverse':'4ba832b67dad4313943db3c9199e3134e56100dbb978db00fd25a7b4eada51d9',
 'YoungParticleMoves':'65f5b6efd9f9799fd2d342d9245bab366cb5da9b022af5b895dc7acbbadf953d',
 'YoungParticleHops':'cbb75e17575148b7e9fdd2bfb844c50094b78f48badd796d661eeaac25423666'}
for mod in mods:
 p=F/'analysis/MathResearchAnalysis'/(mod+'.lean')
 assert sha(p)==expected_hashes[mod]
 assert p.read_bytes()==(F/'drafts'/(mod+'.lean')).read_bytes(),mod
stages=[];covered=[]
for pfx in sorted(A.glob('young-*-declarations-validation.json')):
 d=load(pfx)
 if not set(d['modules'])&set(mods):continue
 assert set(d['modules'])<=set(mods)
 prefix=pfx.name.removesuffix('-declarations-validation.json')
 names=[];kcounts={}
 for mod in d['modules']:
  covered.append(mod)
  p=F/'analysis/MathResearchAnalysis'/(mod+'.lean')
  decls=source_names(p,('theorem','lemma','def','abbrev','instance'))
  names.extend(n for n,k in decls)
  kcounts[mod]={k:sum(kk==k for n,kk in decls) for k in sorted({kk for n,kk in decls})}
  assert sha(p)==d['source_sha256'][p.relative_to(F/'analysis').as_posix()]
 table=A/(prefix+'-declarations-axioms.lean');log=A/(prefix+'-declarations-axioms.log');build=A/(prefix+'-declarations-build.log')
 tab=re.findall(r'^#print axioms (\S+)\s*$',read(table),re.M);outs,axs=actual_names(log)
 assert names==d['named_declarations']==tab==outs,prefix
 assert len(names)==d['declarations_count']
 assert d['build_exit']==d['axiom_audit_exit']==d['kernel_trust_level']==0
 assert d['new_lean_warning_lines']==[]
 assert read(build).rstrip().endswith('EXIT_CODE=0')
 assert axs==set(d['axioms_seen'])
 stages.append({'prefix':prefix,'modules':d['modules'],'validated_at':d['validated_at'],
  'declaration_kinds':kcounts,'names_from_source_table_and_actual_output_exact':True,
  'draft_formal_bytes_exact':True,'count':len(names),'axioms':sorted(axs),
  'names_order_sha256':hashlib.sha256(('\n'.join(names)+'\n').encode()).hexdigest(),
  'table_sha256':sha(table),'log_sha256':sha(log),'build_log_sha256':sha(build),'validation_sha256':sha(pfx)})
assert sorted(covered)==sorted(mods)
assert sorted(s['count'] for s in stages)==[18,24,34]
assert sum(s['count'] for s in stages)==76
baseline=A/'history/before-young-particles-stage-2026-10-25/analysis-validation.json'
before=load(baseline)
assert before['public_theorems']==2889 and before['project_lean_files']==217
old_changes=[k for k,v in before['source_sha256'].items() if anow.get(k)!=v]
assert old_changes==['MathResearchAnalysis.lean'],old_changes
added=sorted(set(anow)-set(before['source_sha256']))
assert added==sorted('MathResearchAnalysis/'+m+'.lean' for m in mods),added
assert analysis['public_theorems']-before['public_theorems']==67
report=A/'young-encoding-independent-review.md'
assert report.exists()
earlier=[]
for fname,nmods in [('sync-lower-independent-final-binding-evidence.json',4),('mixed-square-independent-final-binding-evidence.json',3),('young-rows-independent-final-binding-evidence.json',1)]:
 q=A/fname;prev=load(q)
 assert len(prev['new_source_sha256'])==nmods
 for name,h in prev['new_source_sha256'].items():assert anow[name]==h
 earlier.append({'path':fname,'sha256':sha(q),'all_reviewed_source_sha256_unchanged':True,'modules':list(prev['new_source_sha256'])})
result={'bound_at':datetime.now(timezone(timedelta(hours=8))).isoformat(),
 'reviewer':'/root/sync_profile_review','status':'PASS two-sided finite Young/ordered-particle encoding and bidirectional actual adjacent local transition coverage; rate-summed generator and probability upper core unproved',
 'semantic_review_modules':mods,'self_authored_reviewed_modules':[],
 'independence_note':'Reviewer authored none of the five modules. Independent AI review is not human expert certification.',
 'semantic_review_sha256':sha(report),'independent_binding_script_sha256':sha(Path(__file__)),
 'analysis':analysis,'core':core,'core_rebuilt_in_this_phase':False,
 'core_old_validation_reused_only_after_all_eight_sources_rechecked':True,
 'total_formal_sources':analysis['sources']+core['sources'],
 'complete_actual_global_axiom_outputs_verified':analysis['count']+core['count'],
 'new_stage_theorems':67,'new_stage_named_declarations':76,'new_stage_records':stages,
 'new_source_sha256':{'MathResearchAnalysis/'+m+'.lean':expected_hashes[m] for m in mods},
 'previous_analysis_validation_sha256':sha(baseline),
 'unchanged_previous_analysis_proof_modules':len(before['source_sha256'])-1,
 'previous_sources_changed':['MathResearchAnalysis.lean'],'added_analysis_proof_modules':added,
 'earlier_lower_mixed_young_rows_bindings_unchanged':earlier,
 'all_formal_source_sha256':{'analysis/'+k:v for k,v in anow.items()}|cnow,
 'not_claimed':['actual rate-summed exclusion generator identity','full clock/exclusion process law','cross-size clock restriction law','actual first/second moment equations','quadratic recovery upper bound','complete Theta theorem','human expert certification','novelty certification']}
assert result['total_formal_sources']==230 and result['complete_actual_global_axiom_outputs_verified']==3082
assert result['analysis']['names_with_apostrophes']==3
out=A/'young-encoding-independent-final-binding-evidence.json'
out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(json.dumps({'status':result['status'],'sources':230,'global_axiom_outputs':3082,'new_stage_named':76,
 'old_proof_modules_unchanged':result['unchanged_previous_analysis_proof_modules'],
 'report_sha256':sha(report),'binding_sha256':sha(out),'script_sha256':sha(Path(__file__))},ensure_ascii=False,indent=2))
