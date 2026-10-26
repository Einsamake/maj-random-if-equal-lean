"""Independent read-only binding of the actual mixed moments, off-diagonal covariance, and mean energy audits."""
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

mods=['MixedClockMoments', 'FiniteMomentRegularity', 'PositivePartSquare', 'FiniteExclusionEnergy', 'FinitePermutationComparison', 'MixedMomentEvolution', 'MixedClockCovariance', 'MixedMomentEnergy']
self_authored=['PositivePartSquare']
expected_hashes={'MixedClockMoments': 'aa0a21d873c640250a834fd8fc638c40eafb44f139fb7ba17d655069551dc17f', 'FiniteMomentRegularity': 'f42002733d345aa3c3da012ee4fa64430acce9bd84d4ad224d22008bce78293e', 'PositivePartSquare': 'e79122c726f1c76073da35e28e0396c7977bed04bfbff9b887c6d37190f741d4', 'FiniteExclusionEnergy': 'd21596570a6fc66b0f84e04b5508eba06e3f82eca369c2a450295cf947e7f9eb', 'FinitePermutationComparison': '60d401a0708168d8c84cb23b8a21b91ce6d51187790747dbe06cbd94c33d0f00', 'MixedMomentEvolution': '607c3ba4bf08dae7977a2522de2069d171f63c414c9c71dd1a429b069629567e', 'MixedClockCovariance': '6c6ba7d5702153a79caeca65d26b23a38778e96416103d3e338f92bce4947854', 'MixedMomentEnergy': 'a527c1b0ebd66c3928a16427e37dce1fbb2f294be54ab4fcb9d9e5291fecf104'}
analysis,anow=bind_group('analysis',F/'analysis','MathResearchAnalysis','MathResearchAnalysis.lean',A/'analysis-validation.json',F/'analysis/AnalysisAxioms.lean',A/'analysis-axioms.log',A/'analysis-build.log')
core,cnow=bind_group('core',F,'MathResearch','MathResearch.lean',A/'core-validation.json',A/'CoreAxioms.lean',A/'core-axioms.log',A/'core-build.log',['MathResearch.Grid.system'])
for mod in mods:
 p=F/'analysis/MathResearchAnalysis'/(mod+'.lean')
 assert sha(p)==expected_hashes[mod],mod
 assert p.read_bytes()==(F/'drafts'/(mod+'.lean')).read_bytes(),mod
stages=[];covered=[]
for record in sorted(A.glob('mixed-moments-*-declarations-validation.json')):
 d=load(record)
 if not set(d['modules'])&set(mods):continue
 assert set(d['modules'])<=set(mods)
 prefix=record.name.removesuffix('-declarations-validation.json')
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
  'table_sha256':sha(table),'log_sha256':sha(log),'build_log_sha256':sha(build),'validation_sha256':sha(record)})
assert sorted(covered)==sorted(mods)
baseline=A/'history/before-mixed-moments-stage-2026-10-26/analysis-validation.json'
before=load(baseline)
previous=A/'finite-machine-independent-final-binding-evidence.json';prev=load(previous)
assert sha(baseline)==prev['analysis']['validation_sha256']
assert before['source_sha256']=={k.removeprefix('analysis/'):v for k,v in prev['all_formal_source_sha256'].items() if k.startswith('analysis/')}
assert cnow=={k:v for k,v in prev['all_formal_source_sha256'].items() if not k.startswith('analysis/')}
old_changes=[k for k,v in before['source_sha256'].items() if anow.get(k)!=v]
assert old_changes==['MathResearchAnalysis.lean'],old_changes
added=sorted(set(anow)-set(before['source_sha256']))
assert added==sorted('MathResearchAnalysis/'+m+'.lean' for m in mods),added
newtheorems=sum(len(source_names(F/'analysis/MathResearchAnalysis'/(m+'.lean'))) for m in mods)
newnamed=sum(len(source_names(F/'analysis/MathResearchAnalysis'/(m+'.lean'),('theorem','lemma','def','abbrev','instance'))) for m in mods)
assert analysis['sources']==before['project_lean_files']+len(mods)
assert analysis['public_theorems']==before['public_theorems']+newtheorems
assert newnamed==sum(s['count'] for s in stages)
report=A/'mixed-moments-independent-review.md';assert report.exists()
earlier=[]
for fname in ['sync-lower-independent-final-binding-evidence.json','mixed-square-independent-final-binding-evidence.json','young-rows-independent-final-binding-evidence.json','young-encoding-independent-final-binding-evidence.json','exclusion-independent-final-binding-evidence.json','finite-machine-independent-final-binding-evidence.json']:
 q=A/fname;pr=load(q)
 for name,h in pr['new_source_sha256'].items():assert anow[name]==h
 earlier.append({'path':fname,'sha256':sha(q),'all_reviewed_source_sha256_unchanged':True,'modules':list(pr['new_source_sha256'])})
result={'bound_at':datetime.now(timezone(timedelta(hours=8))).isoformat(),
 'reviewer':'/root/sync_profile_review','status':'PASS actual mixed-clock moment equations, positive-time ODEs, off-diagonal covariance nonpositivity, and centered energy; final upper bound remains unproved',
 'semantic_review_modules':[m for m in mods if m not in self_authored],
 'self_authored_modules_not_independently_semantically_reviewed_by_this_agent':self_authored,
 'root_independently_read_self_authored_module':['PositivePartSquare'],
 'independence_note':'Reviewer authored PositivePartSquare and did not independently certify its semantics; root independently read that module. Reviewer authored none of the seven other modules. All eight source/output bindings are checked here. Independent AI review is not human expert certification.',
 'semantic_review_sha256':sha(report),'independent_binding_script_sha256':sha(Path(__file__)),
 'actual_first_and_second_moments_use_same_original_sample':True,
 'actual_ode_regularities_derived_from_integral_system_not_assumed':True,
 'finite_permutation_comparison_structural_premises_discharged_in_actual_covariance':True,
 'offdiagonal_pair_domain_invariant_and_diagonal_excluded':True,
 'covariance_source_subtracted_and_proven_nonnegative':True,
 'actual_centered_mass_and_energy_rate_constants_checked':True,
 'actual_law_clock_dimension_is_original_parameter_L_not_arbitrary_n':True,
 'integrability_proved_before_signed_integral_sum_exchange':True,
 'analysis':analysis,'core':core,'core_rebuilt_in_this_phase':False,
 'core_old_validation_reused_only_after_all_eight_sources_rechecked':True,
 'total_formal_sources':analysis['sources']+core['sources'],
 'complete_actual_global_axiom_outputs_verified':analysis['count']+core['count'],
 'new_stage_theorems':newtheorems,'new_stage_named_declarations':newnamed,'new_stage_records':stages,
 'new_source_sha256':{'MathResearchAnalysis/'+m+'.lean':expected_hashes[m] for m in mods},
 'previous_analysis_validation_sha256':sha(baseline),
 'previous_phase_binding_sha256':sha(previous),
 'unchanged_previous_analysis_proof_modules':len(before['source_sha256'])-1,
 'previous_sources_changed':['MathResearchAnalysis.lean'],'added_analysis_proof_modules':added,
 'earlier_lower_mixed_rows_young_encoding_exclusion_bindings_sources_unchanged':earlier,
 'all_formal_source_sha256':{'analysis/'+k:v for k,v in anow.items()}|cnow,
 'not_claimed':['stochastic heat decay','particle-count variance and concentration bound','full clock/exclusion process law','cross-size clock restriction law','quadratic recovery upper bound','complete Theta theorem','human expert certification','novelty certification']}
assert result['analysis']['names_with_apostrophes']==3
out=A/'mixed-moments-independent-final-binding-evidence.json'
out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(json.dumps({'status':result['status'],'sources':result['total_formal_sources'],
 'global_axiom_outputs':result['complete_actual_global_axiom_outputs_verified'],
 'new_stage_theorems':newtheorems,'new_stage_named':newnamed,
 'old_proof_modules_unchanged':result['unchanged_previous_analysis_proof_modules'],
 'report_sha256':sha(report),'binding_sha256':sha(out),'script_sha256':sha(Path(__file__))},ensure_ascii=False,indent=2))
