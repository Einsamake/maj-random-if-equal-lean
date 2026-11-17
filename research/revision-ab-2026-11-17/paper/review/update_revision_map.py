from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[1];P=R.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paper_hash=sha(R/'paper.md')
q=R/'revision-source-map.json';m=json.loads(q.read_text(encoding='utf-8'))
if 'inherited_pre_integration_record' not in m:
    m['inherited_pre_integration_record']={k:m[k] for k in ['paper_sha256','scope']}
m['paper_sha256']=paper_hash
m['scope']='A1 A2 A3 B1 B2 B3 integrated revision; C1/C2 are reserved for collaborators and not implemented here.'
modules=[];new=[]
for name in ['OriginalRecoveryResults','SharpRecoveryTail','SharpFailureRate','RecoveryMoments','OriginalConsequences']:
    src=P/'lean'/f'{name}.lean';s=src.read_text(encoding='utf-8');ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
    declarations=[]
    for match in re.finditer(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+([\w\u0080-\uffff]+)\b',s,re.M):
        declaration=ns+'.'+match.group(1)
        entry={'path':'../lean/'+src.name,'path_base':'paper directory','sha256':sha(src),
               'declaration':declaration,'line':s[:match.start()].count('\n')+1}
        declarations.append(entry);new.append(entry)
    modules.append({'path':'../lean/'+src.name,'source_sha256':sha(src),'namespace':ns,
                    'named_declarations':len(declarations),'source_location_check':'performed for this map',
                    'kernel_status':'see revision validation and actual build logs; not inferred from source presence'})
old=[x for x in m['declarations'] if not x.get('path','').startswith('../lean/')]
m['declarations']=old+new;m['new_modules']=modules
m['proof_to_artifact']={
 'A1':'FullBlockThreshold and ImprovedOriginalLower; OriginalConsequences.quadratic_bounds',
 'A2':'OriginalRecoveryResults.original_recovery_block_tail',
 'A3':'OriginalConsequences.finite_machine_dynkin and frozen MachineClockGenerator.expected_observable_dynkin_current',
 'B1':'OriginalRecoveryResults.tau_eq_full_square',
 'B2':'SharpRecoveryTail, SharpFailureRate and OriginalConsequences.original_sharp_block_tail/original_sharp_expectation',
 'B3':'RecoveryMoments and OriginalConsequences.original_rpow_le/original_rpow_lt_top/original_exponential_lt_top'}
m['reader_review']='Waived by explicit user instruction on 2026-11-17; no simulated reader pass is claimed.'
m['kernel_check_performed_by_this_script']=False
q.write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
q=R/'edit-record.json';j=json.loads(q.read_text(encoding='utf-8'))
if 'initial_prose_revision' not in j:
    j['initial_prose_revision']={k:v for k,v in j.items() if k not in ['initial_prose_revision','final_integration']}
j['paper_sha256']=paper_hash;j['reader_acceptance']='waived by explicit user instruction on 2026-11-17'
root=json.loads((R/'review/root-edit-pass.json').read_text(encoding='utf-8'))
assert root['paper_sha256']==paper_hash
j['final_integration']={'paper_sha256':paper_hash,'passes':root['passes'],
                        'source':'review/root-edit-pass.json','source_sha256':sha(R/'review/root-edit-pass.json')}
j['independent_mathematical_review']='See revision validation; no new independent review is asserted by this metadata update.'
j['new_Lean_build']='See revision validation and individual actual logs; this file is an editing record.'
q.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':paper_hash,'new_modules':len(modules),'new_named_declarations_mapped':len(new),
                  'all_source_locations':len(old+new)}))
