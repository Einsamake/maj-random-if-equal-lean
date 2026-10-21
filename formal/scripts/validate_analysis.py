"""Build and audit only the local analytic Lean modules, not dependency sources."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone, timedelta

sys.stdout.reconfigure(encoding='utf8')

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL / 'analysis'
BIN = FORMAL / '.tools' / 'lean-4.35.0-rc4-windows' / 'bin'
AUDIT = FORMAL / 'audit'
env = os.environ.copy()
env['PATH'] = str(BIN) + os.pathsep + env.get('PATH', '')


def without_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif depth:
            out.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        else:
            out.append(source[i])
            i += 1
    return ''.join(out)


files = sorted((ROOT / 'MathResearchAnalysis').glob('*.lean')) + [ROOT / 'MathResearchAnalysis.lean']
declarations, hashes, module_counts = [], {}, {}
for path in files:
    before = len(declarations)
    code = without_comments(path.read_text(encoding='utf8'))
    hashes[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code)
    if forbidden or 'debug.skipKernelTC' in code:
        raise RuntimeError(f'Forbidden proof construct: {path.name}: {forbidden}')
    scopes, prefix = [], []
    for line in code.splitlines():
        line = line.strip()
        match = re.match(r'namespace\s+(\S+)', line)
        if match:
            names = match.group(1).split('.')
            scopes.append(len(names))
            prefix += names
            continue
        if re.match(r'(?:@\[[^\]]*\]\s*)?(?:(?:public|noncomputable)\s+)*section(?:\s|$)', line):
            scopes.append(0)
            continue
        if re.match(r'end(?:\s|$)', line):
            if scopes:
                count = scopes.pop()
                if count:
                    prefix = prefix[:-count]
            continue
        match = re.match(r'(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:theorem|lemma)\s+(\S+)', line)
        if match:
            declarations.append('.'.join(prefix + [match.group(1)]))
    module_counts[path.relative_to(ROOT).as_posix()] = len(declarations) - before

assert declarations and len(declarations) == len(set(declarations))
AUDIT.mkdir(exist_ok=True)
audit_source = ROOT / 'AnalysisAxioms.lean'
audit_source.write_text('import MathResearchAnalysis\n\n' + '\n'.join(
    f'#print axioms {name}' for name in declarations) + '\n', encoding='utf8')


def run(args, filename):
    proc = subprocess.run([str(BIN / 'lake.exe'), *args], cwd=ROOT, env=env,
                          capture_output=True, text=True, encoding='utf8', errors='replace')
    output = proc.stdout + proc.stderr
    (AUDIT / filename).write_text(output + f'\nEXIT_CODE={proc.returncode}\n', encoding='utf8')
    print(output, end='')
    if proc.returncode:
        raise RuntimeError(f'{args} failed with exit {proc.returncode}')
    return output


compiler = subprocess.run([str(BIN / 'lean.exe'), '--version'], env=env,
                          capture_output=True, text=True, encoding='utf8', check=True).stdout.strip()
if 'version 4.35.0-rc4' not in compiler:
    raise RuntimeError(f'Wrong analytic compiler: {compiler}')
mathlib = ROOT / '.lake' / 'packages' / 'mathlib'
commit = subprocess.run(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'],
                        capture_output=True, text=True, encoding='utf8', check=True).stdout.strip()
if commit != '54c01c3314d33d15d77893cbe4e0472ff26bb34d':
    raise RuntimeError(f'Wrong mathlib commit: {commit}')
build = run(['build'], 'analysis-build.log')
axioms = run(['env', 'lean', '--trust=0', 'AnalysisAxioms.lean'], 'analysis-axioms.log')
if 'sorryAx' in axioms or 'error:' in axioms:
    raise RuntimeError('Axiom audit failed')
dependencies = []
for body in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', axioms):
    dependencies += [part.strip() for part in body.split(',') if part.strip()]
unexpected = set(dependencies) - {'propext', 'Classical.choice', 'Quot.sound'}
if unexpected:
    raise RuntimeError(f'Unexpected axioms: {sorted(unexpected)}')
for name in declarations:
    if f"'{name}' depends on axioms:" not in axioms and \
            f"'{name}' does not depend on any axioms" not in axioms:
        raise RuntimeError(f'Missing axiom output for {name}')
summary = {
    'validated_at': datetime.now(timezone(timedelta(hours=8))).isoformat(),
    'compiler': 'Lean 4.35.0-rc4',
    'compiler_output': compiler,
    'mathlib_commit': commit,
    'public_theorems': len(declarations), 'project_lean_files': len(files),
    'theorems_by_module': module_counts,
    'build_exit': 0, 'axiom_audit_exit': 0,
    'kernel_trust_level': 0,
    'axiom_audit_command': 'lake env lean --trust=0 AnalysisAxioms.lean',
    'axioms_seen': sorted(set(dependencies)), 'custom_axioms': False,
    'admitted_holes': False, 'source_sha256': hashes,
    'scope': 'actual clock words, rank tails, marks, finite-word PW and zero-temperature integrals; actual finite-square and infinite-grid random processes with measurable ENat recovery; exact whole-field restriction and recovery laws; translation and complemented-background laws; genuine past/future independence, synchronous restart, actual multiplicative and block tails; two-way clock/grid recovery comparisons; original minimum translated-square diameter, both homogeneous targets, exact-diameter worst ENNReal expectations, finite-pattern normalization and attained maxima for all sizes; exact size-zero/one recovery; finite strict-majority peeling with proved termination, greatest stable core and order-independent terminal deletions, connected to actual infinite-grid and finite-square single updates; actual centered clipped mask, uniform four-quadrant block counts, cleanup-stable clipped initial state and exact centered finite-square representation, including conjugacy of masked raw event words with actual finite cellUpdate; mask-preserving cleanup-after-update finite words with same-mark domination; actual finite/centered cleanup and modified-word conjugacy; different-domain same-mark finite-word comparison with event-index first loss and correctly frozen prefix; actual rate-one-clock/fair-mark droplet endpoint law, word-fiber factorization and unconditional mixture; whole-square raw endpoint equal to the original endpoint and physical-time protected-loss probability comparison; concrete CMST inner diamond and external four-neighbour boundary, exact closed band, finite protected vertices and actual original-process extinction comparison without arbitrary protected I; actual exposed half-edge geometry, exact initial sections/perimeter/bounding-box spans, initial four-connectivity and no-checkerboard, actual boundary connectivity and one full successor cycle with injective vertices, complete real segments with endpoint-only intersections, generic row-convex/four-connected no-checkerboard; actual finite occupied-region frontier equals every exposed full real segment, explicit continuous simple closed initial boundary, exact original unit-cell homeomorphism, actual minimum region/frontier rectangle, genuine Euclidean extended arc length from all finite partitions, actual initial geometric Good certificate; actual row/column-convex stable local raw and modified update classification, birth convexity/stability/connectivity/projection preservation, exact local erase and conditional two-site cleanup criteria, legal cleanup preservation of interval convexity and four-connectivity, actual perimeter insert/erase identities and majority-word Lyapunov law without shape assumptions, cumulative extra cleanup deletion budget and its exact genuine physical-clock endpoint instance; actual protected corner/deletion connectivity and discrete Shape evolution up to and including exit, vacant-quadrant exit area at least L^2/1600, general projection/perimeter/minimum physical rectangle; general true boundary connectivity from column convexity and four-connectivity, single successor cycle, injective full real traversal, entire actual unitRegion frontier and Euclidean eVariationOn length equal to the actual perimeter; discrete Shape with support and inner diamond implies the existing GeometricGood, and real modified/stopped event trajectories satisfy it strictly before protected exit including infinite exit; actual first-loss-frozen word executor equals the ENat stoppedTrajectory with exact all-prefix loss and fallback independence, actual fixed-physical-time frozen endpoint measurable law, word-fiber factorization, unconditional mixture, concrete protected survival measurability and original extinction bounded by frozen historical loss; actual cross-physical-time chronological word prefixes with identity-preserved marks, frozen state consistency and persistent loss on one common almost-sure set for all real times, genuine initial state and right-local constancy from finite future-event gaps, monotone frozen-loss measure; actual ENNReal physical first-loss time defined as the infimum of nonnegative loss times, exact almost-sure nonnegative threshold law, retained infinite no-loss case, finite first-loss attainment and permanent freezing, positive actual exit, null-measurable actual protected exit events, physical-before-exit Good and physical-after-exit quadratic missing area, original clock extinction bounded by physical protected first loss; actual minimal joint arrival/revealed-mark filtration, stopping status of individual arrivals, measurable Option Bool revealed mark field with explicit discrete codomain, pointwise invariance of all history events under indistinguishable past observations, history-measurable finite arrival coverage and local finiteness; past-measurable censored arrival order and complete finite identity-and-mark fibers, a genuinely history-measurable observed loss agreeing with actual frozen loss on clock-good samples; an ENNReal rational-loss infimum is a stopping time in the explicit right-continuation of the joint history, equal almost surely to physicalExit with identical actual law and extended mean; a unique countable complete-state graph gives a genuinely adapted frozen-state representative in both joint history and its right continuation, agrees with the actual state at all real times on one common full-measure set, has genuine initial state and almost-sure right local constancy, and retains pre-exit Good and post-exit quadratic missing area; actual all-sample progressive measurability of the state in restricted time-history products, strong progressive measurability of real missing area and measurable stopped exit area with its physical meaning only under finite exit; exact masked negative-cardinality rate algebra, cleanup contribution and nonnegative forbidden-birth mask correction, without an asserted physical-time compensation formula; genuine deterministic Exp(1) residual waiting independent of the marked joint history, by fixed-mark sections and the actual product measure; all-sample finite-site right event gaps, complete-history prefix consistency and an independent absorbing invalid-history flag yield a genuine original-joint-history exit stopping time equal almost surely to physicalExit with the same ENNReal law and extended mean; arbitrary nonnegative almost-surely finite original-joint-history stopping times have actual single-site Exp(1) residual law independent of their stopped history, proved by measurable fixed-mark stopped sections and actual AE Fubini; the actual exit capped at every finite deterministic horizon instantiates that law without assuming finiteness of the unbounded exit; observed frozen states retain actual mask support, the mask-relative missing area is bounded and integrable, and its exact finite rate agrees with the negative-cardinality rate only after support is proved; single unrevealed identity-mark replacement preserves original past, stopping time and stopped sigma; actual fair coordinate-flip symmetry and disjoint candidate decomposition yield a genuine fair next site-ring mark, with its full restricted law and independence of the stopped past, plus an exact joint survival factorization with the actual Exp(1) residual wait; full residual-wait/next-mark restricted product law and independence from the stopped history, established directly for arbitrary Borel waiting events rather than inferred from marginals; actual bounded protected exit instantiates these laws without assuming unbounded-exit finiteness; genuine original-history arrival and marked counts retain infinity, are jointly measurable at measurable bounded observation times, locally finite almost surely, and admit exact nonnegative Tonelli expectation series; actual lower tails bound the (k+1)th arrival and yield finite count expectations at every finite horizon, including actual capped protected exit, before taking real representatives; actual clipped-gap occupation partitions every nonnegative finite horizon almost surely, and layercake proves the truncated unit-exponential mean; actual deleted-gap/rest product integration converts exposure to arrival mass, yielding exact actual ENNReal count expectation equal to elapsed time and its real integral version; actual independent fair-coordinate mark integration gives exact each-color count mean equal to half the time under the original product law; resetting any still-future gap preserves all original clock and joint marked history events, including when its preceding ring is also future; actual interval counts retain infinity and have genuine finite-horizon integrability; fixed-gap occupation increments on any original clock-history event equal the actual corresponding arrival mass, using the true deleted-gap product law and only support-local past invariance; fixed-mark sections transport this to the original joint history, and finite telescoping plus nonnegative Tonelli yield actual conditional interval means (t-s) times past-event mass, with each preassigned fair mark contributing one half; real count differences are identified only after actual almost-sure finiteness; actual positive marked arrivals up to each finite horizon define a genuine finite point measure on nonnegative time times the original sample, with total mass T/2 and exact nonnegative integral equal to the original pathwise event sum; this asserts concentration on (0,T], not topological support or full ambient product compensation; the actual marked point measure has exact original-history future-generator rectangle masses (T-s)/2 times past-event mass, including beyond-horizon zero and pointwise zero-time rectangles; full predictable-sigma measure equality and continuous predictable-integrand compensation remain unproved; not a claim of pointwise adaptedness of the old globally guarded total word, equality of the joint filtration with its right continuation, full stopped multi-site future-vector independence, generator/compensation theorem, self-contained quadratic-scale CMST/FSS bounds or the full CA theorem',
    'build_warning_lines': [line for line in build.splitlines() if 'warning:' in line],
}
(AUDIT / 'analysis-validation.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding='utf8')
print(json.dumps({k: v for k, v in summary.items() if k != 'source_sha256'}, ensure_ascii=False))
