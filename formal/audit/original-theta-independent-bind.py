"""Independent binding of the complete original synchronous quadratic theorem to actual Lean outputs."""
from pathlib import Path
from datetime import datetime, timezone, timedelta
import hashlib, json, re, sys
sys.stdout.reconfigure(encoding='utf8')
F=Path(__file__).resolve().parents[1]
A=F/'audit'
P=F/'analysis'
MODS=['FiniteSlotPoincare', 'MixedMomentPoincare', 'ScalarHeatDecay', 'CountLowerTail', 'MixedHeatDecay', 'MixedRightCountMoments', 'MixedRightCountHeat', 'MixedLocalClearing', 'MixedClearingProbability', 'ClockSampleRestriction', 'ClockWordRestriction', 'SquareInclusion', 'ClockRestrictedExecution', 'ClockEndpointSurvival', 'CrossSquareClockBound', 'SyncUpperScale', 'OriginalQuadraticUpper', 'OriginalQuadraticRecovery']
PREFIXES=['mixed-heat-path-stage', 'mixed-heat-count-stage', 'mixed-heat-mean-stage', 'mixed-heat-local-stage', 'mixed-heat-probability-stage', 'mixed-clock-restriction-law-stage', 'mixed-clock-restriction-word-stage', 'cross-square-inclusion-stage', 'cross-square-execution-stage', 'cross-square-survival-stage', 'cross-square-clock-bound-stage', 'sync-upper-scale-stage', 'original-sync-upper-stage', 'original-theta-stage']
ALLOWED={'Classical.choice','Quot.sound','propext'}
def read(p):return p.read_text(encoding='utf-8-sig')
def load(p):return json.loads(read(p))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def hash_names(ns):return hashlib.sha256(('\n'.join(ns)+'\n').encode('utf8')).hexdigest()

def uncomment(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;out.append(' ');i+=2
        elif depth and s.startswith('-/',i):depth-=1;out.append(' ');i+=2
        elif depth:
            if s[i]=='\n':out.append('\n')
            i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)

def declarations(p,kinds=('theorem','lemma')):
    code=uncomment(read(p))
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',code),p
    assert 'debug.skipKernelTC' not in code,p
    scopes=[];ns=[];ans=[]
    for raw in code.splitlines():
        ln=re.sub(r'^(?:@\[[^\]]*\]\s*)+','',raw.strip())
        ln=re.sub(r'^(?:(?:public|noncomputable)\s+)+','',ln)
        m=re.match(r'namespace\s+(\S+)',ln)
        if m:scopes.append(ns.copy());ns+=m[1].split('.');continue
        if re.match(r'section(?:\s|$)',ln):scopes.append(ns.copy());continue
        if re.match(r'end(?:\s|$)',ln):
            if scopes:ns=scopes.pop()
            continue
        m=re.match(r'('+('|'.join(kinds))+r')\s+(\S+)',ln)
        if m:ans.append(('.'.join(ns+[m[2]]),m[1]))
    return ans

def actual(log):
    text=read(log)
    assert text.rstrip().endswith('EXIT_CODE=0'),log
    assert 'sorryAx' not in text and 'error:' not in text,log
    # Greedy name capture deliberately preserves apostrophes inside Lean names.
    rows=list(re.finditer(r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M))
    names=[r[1] for r in rows]
    axs={v.strip() for r in rows if r[2] for v in r[2].split(',') if v.strip()}
    assert names and len(names)==len(set(names)),log
    assert axs<=ALLOWED,(log,axs)
    return names,axs

def bind_global(project,folder,entry,record,table,log,build,extra=()):
    d=load(record)
    paths=sorted((project/folder).glob('*.lean'))+[project/entry]
    hashes={p.relative_to(project).as_posix():sha(p) for p in paths}
    assert hashes==d['source_sha256'],record
    assert len(paths)==d['project_lean_files']
    assert d['build_exit']==d['axiom_audit_exit']==d['kernel_trust_level']==0
    assert d['custom_axioms'] is False and d['admitted_holes'] is False
    assert '--trust=0' in d['axiom_audit_command']
    buildtext=read(build)
    assert buildtext.rstrip().endswith('EXIT_CODE=0'),build
    warns=[ln for ln in buildtext.splitlines() if 'warning:' in ln and 'batteries:' not in ln]
    assert warns==[],(build,warns)
    names=[n for p in paths for n,k in declarations(p)]+list(extra)
    listed=re.findall(r'^#print axioms (\S+)\s*$',read(table),re.M)
    printed,axs=actual(log)
    assert names==listed==printed,(record,len(names),len(listed),len(printed))
    assert len(names)==d['public_theorems']+d.get('additional_model_definitions',0)
    assert axs==set(d['axioms_seen'])
    result={'validated_at':d['validated_at'],'sources':len(paths),'public_theorems':d['public_theorems'],
      'additional_model_definitions':d.get('additional_model_definitions',0),'count':len(names),
      'all_source_set_and_sha_exact':True,'source_declarations_match_actual_output':True,
      'all_printed_names_and_order_exact':True,'names_with_apostrophes':sum("'" in n for n in names),
      'names_order_sha256':hash_names(names),'axioms':sorted(axs),'kernel_trust_level':0,
      'validation_sha256':sha(record),'table_sha256':sha(table),'log_sha256':sha(log),'build_log_sha256':sha(build)}
    return result,hashes

HEAT_MODS=['FiniteSlotPoincare', 'MixedMomentPoincare', 'ScalarHeatDecay', 'CountLowerTail', 'MixedHeatDecay', 'MixedRightCountMoments', 'MixedRightCountHeat', 'MixedLocalClearing', 'MixedClearingProbability', 'ClockSampleRestriction', 'ClockWordRestriction']
FINAL_MODS=['SquareInclusion', 'ClockRestrictedExecution', 'ClockEndpointSurvival', 'CrossSquareClockBound', 'SyncUpperScale', 'OriginalQuadraticUpper', 'OriginalQuadraticRecovery']

report=A/'original-theta-independent-review.md'
text=read(report)
assert '工作稿' not in text and '十八份' in text
expected=dict(re.findall(r'^- `([^`]+)`: `([0-9a-f]{64})`',text,re.M))
assert set(expected)==set(MODS)
analysis,anow=bind_global(P,'MathResearchAnalysis','MathResearchAnalysis.lean',A/'analysis-validation.json',P/'AnalysisAxioms.lean',A/'analysis-axioms.log',A/'analysis-build.log')
core,cnow=bind_global(F,'MathResearch','MathResearch.lean',A/'core-validation.json',A/'CoreAxioms.lean',A/'core-axioms.log',A/'core-build.log',('MathResearch.Grid.system',))
for m in MODS:
    src=P/'MathResearchAnalysis'/(m+'.lean')
    assert sha(src)==expected[m],m
    assert src.read_bytes()==(F/'drafts'/(m+'.lean')).read_bytes(),m

def archive_check(folder):
    hist=A/'history'/folder;manifest=load(hist/'archive-manifest.json')
    for name,h in manifest.items():assert sha(hist/Path(name))==h,(folder,name)
    return hist,sha(hist/'archive-manifest.json')

hist,manifest_sha=archive_check('before-cross-square-stage-2026-10-26')
baseline=hist/'audit/analysis-validation.json';before=load(baseline)
previous=hist/'audit/mixed-heat-independent-final-binding-evidence.json';prev=load(previous)
assert sha(baseline)==prev['analysis']['validation_sha256']
assert before['source_sha256']=={k.removeprefix('analysis/'):v for k,v in prev['all_formal_source_sha256'].items() if k.startswith('analysis/')}
assert cnow=={k:v for k,v in prev['all_formal_source_sha256'].items() if not k.startswith('analysis/')}
assert sha(A/'mixed-heat-independent-final-binding-evidence.json')==sha(previous)
changes=[k for k,v in before['source_sha256'].items() if anow.get(k)!=v]
assert changes==['MathResearchAnalysis.lean'],changes
added=sorted(set(anow)-set(before['source_sha256']))
assert added==sorted('MathResearchAnalysis/'+m+'.lean' for m in FINAL_MODS)
assert analysis['sources']==before['project_lean_files']+len(FINAL_MODS)

older,older_manifest_sha=archive_check('before-mixed-heat-stage-2026-10-26')
older_record=older/'audit/analysis-validation.json';older_before=load(older_record)
older_previous=older/'audit/mixed-moments-independent-final-binding-evidence.json';older_prev=load(older_previous)
assert sha(older_record)==older_prev['analysis']['validation_sha256']
assert [k for k,v in older_before['source_sha256'].items() if anow.get(k)!=v]==['MathResearchAnalysis.lean']
assert sorted(set(anow)-set(older_before['source_sha256']))==sorted('MathResearchAnalysis/'+m+'.lean' for m in MODS)
for name,h in prev['new_source_sha256'].items():assert anow[name]==h

stages=[];covered=[];all_named=[]
for prefix in PREFIXES:
    record=A/(prefix+'-declarations-validation.json');d=load(record)
    assert set(d['modules'])<=set(MODS),prefix
    names=[];counts={}
    for m in d['modules']:
        covered.append(m);src=P/'MathResearchAnalysis'/(m+'.lean')
        decls=declarations(src,('theorem','lemma','def','abbrev','instance'))
        names.extend(n for n,k in decls)
        counts[m]={k:sum(kk==k for n,kk in decls) for k in sorted({kk for n,kk in decls})}
        assert sha(src)==d['source_sha256'][src.relative_to(P).as_posix()],prefix
    table=A/(prefix+'-declarations-axioms.lean');log=A/(prefix+'-declarations-axioms.log');build=A/(prefix+'-declarations-build.log')
    listed=re.findall(r'^#print axioms (\S+)\s*$',read(table),re.M);printed,axs=actual(log)
    assert names==d['named_declarations']==listed==printed,prefix
    assert len(names)==d['declarations_count']
    assert d['build_exit']==d['axiom_audit_exit']==d['kernel_trust_level']==0
    assert d['new_lean_warning_lines']==[]
    assert read(build).rstrip().endswith('EXIT_CODE=0')
    assert [ln for ln in read(build).splitlines() if 'warning:' in ln and 'batteries:' not in ln]==[]
    assert axs==set(d['axioms_seen'])
    all_named+=names
    stages.append({'prefix':prefix,'modules':d['modules'],'count':len(names),'validated_at':d['validated_at'],
      'declaration_kinds':counts,'source_table_record_actual_name_order_exact':True,'draft_formal_bytes_exact':True,
      'names_order_sha256':hash_names(names),'axioms':sorted(axs),'validation_sha256':sha(record),
      'table_sha256':sha(table),'log_sha256':sha(log),'build_log_sha256':sha(build)})
assert sorted(covered)==sorted(MODS),(covered,MODS)
def theorem_count(mods):return sum(len(declarations(P/'MathResearchAnalysis'/(m+'.lean'))) for m in mods)
def named_names(mods):return [n for m in mods for n,k in declarations(P/'MathResearchAnalysis'/(m+'.lean'),('theorem','lemma','def','abbrev','instance'))]
newtheorems=theorem_count(FINAL_MODS);heat_theorems=theorem_count(HEAT_MODS)
newnamed=named_names(FINAL_MODS);heat_named=named_names(HEAT_MODS);allnames=named_names(MODS)
assert len(allnames)==len(set(allnames))==len(all_named) and set(allnames)==set(all_named)
assert newtheorems==42 and len(newnamed)==48
assert heat_theorems==65 and len(heat_named)==78
assert analysis['public_theorems']==before['public_theorems']+newtheorems
assert analysis['public_theorems']==older_before['public_theorems']+newtheorems+heat_theorems
assert analysis['sources']+core['sources']==267
assert analysis['count']+core['count']==3406
assert analysis['names_with_apostrophes']==3
assert sum(s['count'] for s in stages[:7])==78
assert sum(s['count'] for s in stages[7:])==48
assert analysis['public_theorems']==3280 and analysis['sources']==259

main='MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic'
main_src=P/'MathResearchAnalysis/OriginalQuadraticRecovery.lean'
main_code=uncomment(read(main_src))
assert re.search(r'theorem\s+tau_theta_quadratic\s*:',main_code)
main_statement=main_code.split('theorem tau_theta_quadratic',1)[1].split(':= by',1)[0].strip()
assert main_statement.startswith(':') and '∃ c C : Real' in main_statement and '∃ N₀ : Nat' in main_statement
assert 'OriginalRecoveryProfile.tau N' in main_statement
assert main in actual(A/'analysis-axioms.log')[0]
assert main in actual(A/'original-theta-stage-declarations-axioms.log')[0]

prior=[]
for fname in ['sync-lower-independent-final-binding-evidence.json','mixed-square-independent-final-binding-evidence.json','young-rows-independent-final-binding-evidence.json','young-encoding-independent-final-binding-evidence.json','exclusion-independent-final-binding-evidence.json','finite-machine-independent-final-binding-evidence.json','mixed-moments-independent-final-binding-evidence.json','mixed-heat-independent-final-binding-evidence.json']:
    q=A/fname;d=load(q)
    for name,h in d['new_source_sha256'].items():assert anow[name]==h,(fname,name)
    prior.append({'path':fname,'sha256':sha(q),'all_reviewed_sources_unchanged':True})

result={'bound_at':datetime.now(timezone(timedelta(hours=8))).isoformat(),'reviewer':'/root/heat_stage_review',
  'status':'PASS complete original synchronous exact-N quadratic asymptotic theorem with explicit eventual constants; no core conclusion supplied as a premise',
  'main_theorem_complete':True,'main_theorem':main,'main_theorem_source_statement':main_statement,
  'main_theorem_has_no_external_parameters_or_core_inputs':True,
  'main_theorem_scope':{'model':'infinite two-dimensional synchronous four-neighbour Maj-Random-If-Equal','scale':'exact smallest translated half-open axis-square side N','worst_mean':'deterministic initial configurations; supremum proved attained','backgrounds':'both homogeneous configurations','infinite_recovery_values_preserved':True,'lower_constant':'1/56623104000','upper_constant':664066,'common_eventual_threshold':786432000,'upper_threshold':16,'standard_eventual_theta_not_all_N_ge_one':True},
  'primary_model_source_directly_read':{'url':'https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf','journal_year':2022,'sections':['1.2 (p31)','4.1 (pp53-54)','4.2 (p54)','Question 7.4 (p79)'],'direct_author_pdf_read_this_phase':True,'arxiv_html_this_phase':'request timed out; no claim of successful HTML read'},
  'semantic_review_modules':MODS,'self_authored_mathematical_modules':[],
  'independence_note':'Reviewer authored none of these eighteen Lean mathematical modules. Independent AI review is not human expert, priority, or novelty certification.',
  'semantic_review_sha256':sha(report),'independent_binding_script_sha256':sha(Path(__file__)),
  'analysis':analysis,'core':core,'core_rebuilt_in_this_phase':False,
  'core_old_validation_reused_only_after_all_eight_sources_rechecked':True,
  'total_formal_sources':267,'complete_actual_global_axiom_outputs_verified':3406,
  'new_stage_theorems':newtheorems,'new_stage_named_declarations':len(newnamed),'new_stage_records':stages[7:],
  'previous_phase_theorems':heat_theorems,'previous_phase_named_declarations':len(heat_named),'previous_phase_stage_records_rebound':stages[:7],
  'all_current_run_new_modules':len(MODS),'all_current_run_new_theorems':newtheorems+heat_theorems,'all_current_run_named_declarations':len(allnames),
  'new_source_sha256':{'MathResearchAnalysis/'+m+'.lean':expected[m] for m in FINAL_MODS},
  'all_current_run_source_sha256':{'MathResearchAnalysis/'+m+'.lean':expected[m] for m in MODS},
  'all_formal_source_sha256':{'analysis/'+k:v for k,v in anow.items()}|cnow,
  'previous_analysis_validation_sha256':sha(baseline),'previous_phase_binding_sha256':sha(previous),
  'archive_manifest_sha256':manifest_sha,'earlier_249_archive_manifest_sha256':older_manifest_sha,'all_archived_evidence_sha_rechecked':True,
  'unchanged_previous_analysis_proof_modules':len(before['source_sha256'])-1,
  'unchanged_249_baseline_analysis_proof_modules':len(older_before['source_sha256'])-1,
  'previous_sources_changed':['MathResearchAnalysis.lean'],'added_analysis_proof_modules':added,
  'earlier_proof_bindings_sources_unchanged':prior,
  'actual_clock_word_law_geometry_and_each_event_coupling_discharged':True,
  'original_clock_survival_time_monotonicity_proved_on_actual_good_words':True,
  'second_direction_of_two_way_sync_clock_comparison_used':True,
  'both_checkerboard_and_scheduling_factors_two_paid':True,
  'actual_original_size_N_not_auxiliary_size_in_scheduling_error':True,
  'block_constant_332033_and_expectation_constant_664066_checked':True,
  'genuine_sync_restart_and_ENNReal_block_integral_no_finiteness_input':True,
  'normalization_removes_all_original_initial_state_background_translation_inputs':True,
  'not_claimed':['the same explicit constants for all N>=1','human expert certification','first-public-solution or novelty certification','exhaustive current literature search','public publication or remote CI execution']}
out=A/'original-theta-independent-final-binding-evidence.json'
out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(json.dumps({'status':result['status'],'sources':267,'global_axiom_outputs':3406,'final_new_theorems':newtheorems,
 'final_named':len(newnamed),'final_groups':len(stages[7:]),'all_current_run_theorems':newtheorems+heat_theorems,'all_current_run_named':len(allnames),
 'old_proof_modules_unchanged':result['unchanged_previous_analysis_proof_modules'],
 'report_sha256':sha(report),'binding_sha256':sha(out),'script_sha256':sha(Path(__file__))},ensure_ascii=False,indent=2))
