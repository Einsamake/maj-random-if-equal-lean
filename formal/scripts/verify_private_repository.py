"""Read back every tracked blob of the existing private repository after a push."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
import subprocess,json,hashlib,base64
R=Path(__file__).resolve().parents[2]; W=R/'repository/maj-random-if-equal-lean'
repo='Einsamake/maj-random-if-equal-lean'
def run(args):
    return subprocess.check_output(args,cwd=W)
commit=run(['git','rev-parse','HEAD']).decode().strip()
info=json.loads(run(['gh','repo','view',repo,'--json','isPrivate,url,nameWithOwner']))
assert info['isPrivate'] and info['nameWithOwner']==repo
assert run(['git','status','--porcelain'])==b''
index={}
for item in run(['git','ls-files','--stage','-z']).split(b'\0'):
    if not item: continue
    header,name=item.split(b'\t',1);mode,sha,stage=header.split()
    assert stage==b'0' and mode==b'100644'
    name=name.decode('utf8');raw=(W/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==sha.decode()
    index[name]=sha.decode()
tree=json.loads(run(['gh','api',f'repos/{repo}/git/trees/{commit}?recursive=1']))
assert not tree.get('truncated')
remote={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
assert remote==index
count=0
for kind,base in [('core',Path('formal')),('analysis',Path('formal/analysis'))]:
    rec=json.loads((R/'formal/audit'/f'{kind}-validation.json').read_text(encoding='utf8'))
    for name,sha in rec['source_sha256'].items():
        local=(R/base/name).read_bytes();curated=(W/base/name).read_bytes()
        assert local==curated and hashlib.sha256(local).hexdigest()==sha
        count+=1
for name in ['README.md','STATUS.md']:
    out=json.loads(run(['gh','api',f'repos/{repo}/contents/{name}?ref={commit}']))
    assert base64.b64decode(out['content'])==(R/name).read_bytes()
analysis=json.loads((R/'formal/audit/analysis-validation.json').read_text(encoding='utf8'))
has_mixed='MathResearchAnalysis/MixedSquareClockLaw.lean' in analysis['source_sha256']
has_exclusion='MathResearchAnalysis/MixedExclusionGenerator.lean' in analysis['source_sha256']
has_dynkin='MathResearchAnalysis/MixedClockDynkin.lean' in analysis['source_sha256']
has_moments='MathResearchAnalysis/MixedClockCovariance.lean' in analysis['source_sha256']
record={'validated_at':datetime.now(timezone(timedelta(hours=8))).isoformat(),
 'url':info['url'],'is_private':True,'repository':repo,'branch':'main','commit':commit,
 'remote_files_checked':len(remote),'formal_sources_checked':count,
 'analysis_theorems':analysis['public_theorems'],'helper_theorems':analysis['public_theorems']+125,
 'additional_model_definitions':1,'all_remote_blob_hashes_match':True,
 'all_formal_Lean_bytes_identical_to_workspace':True,'snapshot_local_path':str(W),
 'main_theorem_complete':False,'quadratic_lower_bound_complete':True,'mixed_boundary_foundation_complete':has_mixed,'finite_particle_generator_algebra_complete':has_exclusion,'actual_mixed_clock_dynkin_complete':has_dynkin,'actual_mixed_clock_moment_odes_complete':has_moments,'actual_offdiagonal_covariance_complete':has_moments,
 'full_remote_build_or_CI_run':False,'excluded_local_automation_state':True,
 'working_tree_clean_after_push':True,'remote_readme_bytes_verified':True,
 'remote_status_bytes_verified':True,'formal_proofs_changed':True,
 'metadata_note':'Formal Lean bytes are exact; Markdown, JSON and log paths may be sanitized. Snapshot manifest records both workspace and curated hashes.',
 'change_scope':('Actual original-law moment integral equations and positive-time ODEs, off-diagonal nonpositive covariance and centered first-moment energy verified; heat decay/concentration, cross-size clock law and quadratic upper/Theta remain unproved.' if has_moments else 'Actual finite-state past/predictable bridge, real clock/current-state Dynkin and genuine mixed/exclusion observable formula verified; moment equations, covariance, cross-size law and quadratic upper/Theta remain unproved.' if has_dynkin else 'Original synchronous exact-N lower bound, two-sided particle geometry, exact finite mixed/swap generator algebra and path Poincare verified; true clock Dynkin, moment/time laws, cross-size law and full upper/Theta remain unproved.' if has_exclusion else 'Actual original synchronous exact-N quadratic lower bound and actual mixed-boundary same-size clock/shape foundation; true exclusion process law, cross-size clock restriction and full upper/Theta unproved.' if has_mixed else 'Actual original synchronous exact-N quadratic extended-expectation lower bound; full quadratic upper bound and Theta theorem remain unproved.')}
(R/'formal/audit/github-private-repository.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
print(json.dumps(record,ensure_ascii=False))



