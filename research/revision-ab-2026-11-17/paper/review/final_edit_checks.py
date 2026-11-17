from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,re,shutil

R=Path(__file__).resolve().parents[1];W=Path('D:/MyWorks/Math')
OLD=W/'research/manuscript/quadratic-recovery-v5'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=R/'paper.md';s=p.read_text(encoding='utf-8');passes=[]
def edit(n,old,new,reason):
    global s
    h=sha(p);assert s.count(old)==1,(n,old[:40]);s=s.replace(old,new)
    p.write_text(s,encoding='utf-8',newline='\n')
    passes.append({'pass':n,'before_sha256':h,'after_sha256':sha(p),'purpose':reason})
edit(1,
     'The extended tail-sum identity gives, before finiteness is known,',
     'The infinite-time event is contained in $\\{T_g>jb_N\\}$ for every $j$, so its probability is at most $2^{-j}$ for every $j$ and is therefore zero. The extended tail-sum identity gives, without a prior integrability assumption,',
     'Check conditions, infinity, and floor arithmetic. Make the almost-sure-finiteness consequence explicit before any finite representative or moments are used.')
edit(2,
     'The improved static cost uses the sum of all weights in a square of side $\\lfloor L/20\\rfloor$, rather than a uniform lower bound on a smaller square. The proof is given in §5.3.',
     'The static cost comes from summing the varying weights over the full square of side $\\lfloor L/20\\rfloor$. Section 5.3 proves the exact affine sum and the floor estimate that yield $L^3/12500$.',
     'Simplify the lower-proof narrative and connect the numerical improvement directly to its calculation instead of contrasting with an abandoned smaller-block estimate.')
edit(3,
     'The companion [source-map.json](source-map.json) fixes the source declarations used here; [edit-record.json](edit-record.json) records the editing passes.',
     'The companion [revision-source-map.json](revision-source-map.json) records the declarations used in the revised sections; [edit-record.json](edit-record.json) records their editing passes. The inherited v5 source maps retain their original provenance.',
     'Check symbols, references and figure correspondence. Separate the current revision map from inherited source maps and preserve provenance.')

for name in ['edit-record-scheduling.json']:
    shutil.copy2(OLD/name,R/name)

entries=[]
for rel,names in [
 ('research/exploration/lean/FullBlockThreshold.lean',['fullBlock_exact_lower_bound','fullBlock_cubic_weight','cubic_weight_of_protected_missing','original_clock_extinction_at_quadraticHorizon_le_half']),
 ('research/exploration/phase2/lean/ImprovedOriginalLower.lean',['rounds_lower_bound','synchronous_tail_ge_quarter','halfSide_ge_third','rounds_quarter_ge_original_square','tau_quadratic_bounds']),
 ('formal/analysis/MathResearchAnalysis/MachineClockDynkin.lean',['expected_observable_dynkin']),
 ('formal/analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean',['tau_eq_normalizedTau','expectedRecovery_finite_square']),
 ('formal/analysis/MathResearchAnalysis/OriginalQuadraticUpper.lean',['recovery_block_tail'])
]:
    src=W/rel;body=src.read_text(encoding='utf-8');ns=re.search(r'^namespace (\S+)',body,re.M).group(1)
    for name in names:
        match=re.search(r'^theorem '+re.escape(name)+r'\b',body,re.M);assert match,(rel,name)
        entries.append({'path':rel,'sha256':sha(src),'declaration':ns+'.'+name,
                        'line':body[:match.start()].count('\n')+1})
constants=[
 {'quantity':'static cubic denominator','v5':128000,'revision6':12500,'condition':'L>=80'},
 {'quantity':'clock horizon denominator','v5':12288000,'revision6':1000000,'condition':'L>=250000 in revision6'},
 {'quantity':'synchronous quotient denominator','v5':196608000,'revision6':8000000,'condition':'q=floor(L^2/denominator), r=q-1'},
 {'quantity':'rounds lower-bound denominator','v5':393216000,'revision6':16000000,'condition':'L>=250000 in revision6'},
 {'quantity':'half-side lower threshold','v5':196608000,'revision6':250000},
 {'quantity':'N-to-half-side factor','v5':6,'revision6':3,'condition':'L=floor((N-1)/2), N>=6'},
 {'quantity':'original lower denominator','v5':56623104000,'revision6':576000000,'condition':'N>=500001 in revision6'},
 {'quantity':'original threshold','v5':786432000,'revision6':500001},
 {'quantity':'upper coefficient','v5':664066,'revision6':664066,'condition':'N>=16'}]
source_map={'paper_sha256':sha(p),'baseline_paper_sha256':sha(OLD/'paper.md'),
 'scope':'A1 A2 A3 B1 prose; B2/B3 and integrated validation handled separately',
 'declarations':entries,'constant_replacements':constants,
 'A3_applications':{'mixed':{'state':'finite coordinatewise-monotone square patterns','closure':'§4.1',
    'observable':'G(f)=F(eta(f))','increment_operator':'MC1'},
    'cleanup':{'state':'pairs (U,c) reachable by finite words, PB16','closure':'append one event',
    'observable':'counter c, then missing weight V(U)','pathwise_budget':'PB13'}},
 'kernel_check_performed_by_this_script':False,'frozen_sources_changed':False}
(R/'revision-source-map.json').write_text(json.dumps(source_map,indent=2)+'\n',encoding='utf-8')
(R/'edit-record.json').write_text(json.dumps({'paper_sha256':sha(p),'passes':passes,
   'reader_acceptance':'pending','independent_mathematical_review':'pending',
   'new_Lean_build':False,'old_v5_mutated':False},indent=2)+'\n',encoding='utf-8')

checks=[]
for L in range(80,10001):
    m=L//20
    assert m>=4 and L<=25*m and m<=Q(L,20)
    assert m*m*(Q(L,10)-m)>=Q(L**3,12500)
checks.append({'kind':'exact rational full-block floor/sum inequalities','L':'80..10000','pass':True})
for L in list(range(250000,260001))+[500000,1000000,10**9]:
    q=L*L//8000000;r=q-1
    assert q>=32 and L<=64*(q-12) and Q(L*L,16000000)<=r
    assert (18*L+12)*Q(L*L,1000000)+(L+2)*(4*L+2)<=Q(L**3,25000)
checks.append({'kind':'exact rational horizon and integer-round inequalities','L':'250000..260000 plus large samples','pass':True})
for N in range(500001,510001):
    L=(N-1)//2;r=L*L//8000000-1
    assert L>=250000 and 2*L+1<=N and Q(N,3)<=L and Q(N*N,576000000)<=Q(r,4)
checks.append({'kind':'exact-size floor and final constant inequalities','N':'500001..510000','pass':True})
tags=re.findall(r'\\tag\{([^}]+)\}',s);assert len(tags)==len(set(tags))
assert len(re.findall(r'^!\[',s,re.M))==6
assert not any(t in s for t in ['128000','56623104000','786432000','MC2','MC3','MC4','MC5','PB18'])
assert sha(OLD/'paper.md')=='2b3411cb3c8f661650b3f1e7390d58aa8d91db10ec2ef75e0e8d9ab8361b59d0'
checks.append({'kind':'unique equation tags, six actual figures, obsolete constants/references absent, old v5 fingerprint','pass':True})
(R/'review/math-and-reference-checks.json').write_text(json.dumps({'paper_sha256':sha(p),'checks':checks,
    'meaning':'Finite arithmetic checks and source-location checks do not replace Lean verification or an independent mathematical review.'},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'paper_sha256':sha(p),'passes':len(passes),'source_declarations':len(entries),'checks':len(checks)}))
