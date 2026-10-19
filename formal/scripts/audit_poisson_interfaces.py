"""A bounded, repeatable local API search, not a theorem nonexistence claim."""
from pathlib import Path
import hashlib
import json
import re

FORMAL = Path(__file__).resolve().parents[1]
MATHLIB = FORMAL / 'analysis' / '.lake' / 'packages' / 'mathlib'
source = MATHLIB / 'Mathlib' / 'Probability'
patterns = {
    'poisson_process': r'PoissonProcess|poisson process',
    'strong_markov': r'StrongMarkov|strong.?markov',
    'censoring_ising': r'\b(?:censoring|Peres|Winkler|Ising|Caputo|Toninelli|Simenhaus)\b',
    'factorial_moment': r'factorial moment',
}
files = sorted(source.rglob('*.lean'))
matches = {key: [] for key in patterns}
for path in files:
    for line_number, line in enumerate(path.read_text(encoding='utf8').splitlines(), 1):
        for key, pattern in patterns.items():
            if re.search(pattern, line, re.I):
                matches[key].append({'path': path.relative_to(MATHLIB).as_posix(),
                    'line': line_number, 'text': line.strip()})
interfaces = ['Mathlib/Probability/Process/Stopping.lean',
    'Mathlib/Probability/Distributions/Exponential.lean',
    'Mathlib/Probability/Distributions/Poisson/Basic.lean',
    'Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean']
record = {
    'mathlib_commit_recorded': '54c01c3314d33d15d77893cbe4e0472ff26bb34d',
    'scope': 'all local Mathlib/Probability Lean files at the installed fixed version',
    'files_searched': len(files), 'patterns': patterns, 'matches': matches,
    'interface_source_sha256': {name: hashlib.sha256((MATHLIB / name).read_bytes()).hexdigest()
        for name in interfaces},
    'conclusion': 'No directly usable Poisson strong-Markov, PW or CMST interface found in this keyword search. This does not prove absence from Lean or from other names.',
}
target = FORMAL / 'audit' / 'poisson-interface-audit.json'
target.write_text(json.dumps(record, ensure_ascii=False, indent=2), encoding='utf8')
print(json.dumps({'files_searched': len(files),
    'match_counts': {key: len(value) for key, value in matches.items()}}, ensure_ascii=False))
