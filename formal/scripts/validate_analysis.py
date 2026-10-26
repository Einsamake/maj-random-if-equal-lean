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
    'main_theorem_complete': 'MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic' in declarations,
    'main_theorem': 'MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic',
    'scope': 'The original infinite synchronous four-neighbour independent fair-tie model, exact original translated-square side, both homogeneous targets and worst extended expectation are preserved. True clock and identity-mark law and word restriction, actual cross-size four-neighbour update coupling, mixed moment/negative covariance/heat/variance and local-clearing probabilities, original clock survival monotonicity, actual scheduling and both checkerboard factors, actual restart and ENNReal block integration now yield the original upper bound tau(N)<=ofReal(664066*N^2) for N>=16. Together with the previously verified lower bound this proves eventual two-sided quadratic bounds with c=1/56623104000, C=664066 and shared threshold 786432000. No core probability, comparison or geometric conclusion is a final theorem premise. Infinity is retained until finite mean is a conclusion. This is the standard eventual Theta statement, not displayed-constant bounds for all positive sizes. No global novelty, human expert certification or remote CI claim.',
    'build_warning_lines': [line for line in build.splitlines() if 'warning:' in line],
}
(AUDIT / 'analysis-validation.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding='utf8')
print(json.dumps({k: v for k, v in summary.items() if k != 'source_sha256'}, ensure_ascii=False))





