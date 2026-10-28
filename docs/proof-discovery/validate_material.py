"""Validate teaching artifacts against frozen project evidence; no Lean build.

Run: python validate_material.py --project D:/MyWorks/Math
Writes only validation.json beside this script.
"""
from pathlib import Path
from datetime import datetime
import argparse
import ast
import hashlib
import json
import re
from urllib.parse import unquote
from PIL import Image

parser = argparse.ArgumentParser()
parser.add_argument('--project', type=Path, required=True)
args = parser.parse_args()
R = args.project.resolve()
HERE = Path(__file__).resolve().parent
assert HERE.parent.name == 'docs' and HERE.name == 'proof-discovery'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


audit_path = R/'formal/audit/analysis-validation.json'
audit = json.loads(audit_path.read_text(encoding='utf-8-sig'))
assert audit['build_exit'] == audit['axiom_audit_exit'] == 0
assert audit['kernel_trust_level'] == 0
assert not audit['custom_axioms'] and not audit['admitted_holes']
analysis = R/'formal/analysis'
for name, expected in audit['source_sha256'].items():
    assert sha(analysis/name) == expected, name
expected_set = set(audit['source_sha256'])
actual_set = {p.relative_to(analysis).as_posix() for p in (analysis/'MathResearchAnalysis').rglob('*.lean')}
actual_set.add('MathResearchAnalysis.lean')
assert actual_set == expected_set
binding_path = R/'formal/audit/original-theta-independent-final-binding-evidence.json'
binding = json.loads(binding_path.read_text(encoding='utf-8-sig'))
for name, expected in binding['all_formal_source_sha256'].items():
    assert sha(R/'formal'/name) == expected, name
assert len(binding['all_formal_source_sha256']) == 267

pack_path = R/'formal/audit/package-validation.json'
pack = json.loads(pack_path.read_text(encoding='utf-8-sig'))
zip_path = R/'deliverables/Lean形式化材料_2026-10-26.zip'
assert sha(zip_path) == pack['sha256']

# Preserve original link bases even when validating staged C-drive documents.
links = []
for p in sorted(HERE.glob('*.md')):
    virtual = R/'docs/proof-discovery'/p.name
    s = p.read_text(encoding='utf-8')
    assert '\ufffd' not in s
    for label, target in re.findall(r'!?\[([^\]]*)\]\(([^)]+)\)', s):
        if target.startswith(('https://', 'http://', '#')):
            continue
        rel = unquote(target.split('#', 1)[0])
        final = (virtual.parent/rel).resolve()
        assert final == R or R in final.parents, target
        staged = HERE/rel
        exists = (rel == 'validation.json' or staged.exists()) if not rel.startswith('../') else final.exists()
        assert exists, f'{p.name}: {target}'
        links.append({'document': p.name, 'target': target})

for p in HERE.glob('*.py'):
    ast.parse(p.read_text(encoding='utf-8'), filename=p.name)
toy_path = HERE/'toy-checks.json'
toy = json.loads(toy_path.read_text(encoding='utf-8'))
reuse = json.loads((HERE/'reuse-validation.json').read_text(encoding='utf-8'))
assert reuse['exit_code'] == 0 and reuse['trust_level'] == 0
assert sha(HERE/'ReuseExample.lean') == reuse['source_sha256']
assert sha(HERE/'reuse-kernel.log') == reuse['log_sha256']
reader_path = HERE/'reader-review.json'
reader = json.loads(reader_path.read_text(encoding='utf-8'))
assert reader['unresolved_blockers'] == []
reviewed = reader['reviewed_file_sha256']
required_reading = {q.name for q in HERE.glob('*.md')}
required_reading.update(q.relative_to(HERE).as_posix() for q in (HERE/'images').glob('*.png'))
assert set(reviewed) == required_reading, 'Reader coverage differs from current chapters and figures'
for name, expected in reviewed.items():
    assert sha(HERE/name) == expected, 'Readability review is stale: '+name
for name, expected in toy['figures'].items():
    p = HERE/'images'/name
    assert sha(p) == expected
    with Image.open(p) as image:
        image.verify()
assert toy['supporting_inequality_rational_pairs'] == 1369
assert toy['exhaustive_encoding_profiles_M_1_through_5'] == 350
assert toy['selected_state_zero_boundary_checks'] == 912

# Claim anchors are declaration checks, not an automated semantic proof.
anchors = {
    'OriginalQuadraticRecovery': ['tau_theta_quadratic', 'tau_quadratic_bounds'],
    'ForbiddenBirthControl': ['outside_birth_layer', 'weight_zero_at_outside_birth', 'actual_rawWeightedRate_eq_square'],
    'PhysicalWeightedDrift': ['actual_mean_weighted_area_le', 'actual_exit_probability_le_linear_time'],
    'PositivePartSquare': ['hasDerivAt_square', 'supporting_inequality'],
    'FinitePermutationComparison': ['permutation_flux_nonpos', 'nonpos'],
    'MixedClockCovariance': ['covariance_nonpos', 'offdiag_moment_le_product'],
    'YoungParticles': ['rightCount_eq_diagonal_card'],
    'MixedLocalClearing': ['localWhite_iff_le_rightCount'],
    'MixedClearingProbability': ['failure_probability_le', 'auxiliary_failure_quarter'],
}
claim_sources = {}
for module, declarations in anchors.items():
    p = analysis/'MathResearchAnalysis'/f'{module}.lean'
    s = p.read_text(encoding='utf-8-sig')
    for name in declarations:
        assert re.search(r'\btheorem\s+'+re.escape(name)+r'\b', s), name
    claim_sources[module] = {'sha256': sha(p), 'declarations': declarations}

histories = [
    'research/followup/METHOD_LEDGER_2026-10-22.md',
    'research/followup/METHOD_LEDGER_2026-10-24.md',
    'research/followup/METHOD_LEDGER_2026-10-25.md',
    'research/followup/METHOD_LEDGER_2026-10-26_MOMENTS.md',
    'research/followup/METHOD_LEDGER_2026-10-26_FINAL.md',
    'research/followup/WEIGHTED_ROUTE_2026-10-24.md',
    'research/followup/MIXED_CLOCK_DYNKIN_ROUTE_2026-10-25.md',
    'formal/audit/forbidden-birth-source-comparison.json',
    'research/followup/NOVELTY_CHECK_2026-10-26.md',
]
artifacts = {p.relative_to(HERE).as_posix(): sha(p)
             for p in sorted(HERE.rglob('*')) if p.is_file() and p.name != 'validation.json'}
record = {
    'checked_at': datetime.now().astimezone().isoformat(),
    'status': 'PASS documentation, exact examples, links and frozen analysis source fingerprints',
    'scope': 'tutorial reconstruction and method candidates; two new teaching declarations checked separately; no rebuilt main theorem or novelty certification',
    'project_root': str(R),
    'analysis_source_hashes_matched': len(expected_set),
    'all_formal_source_hashes_matched': len(binding['all_formal_source_sha256']),
    'prior_build_and_kernel_audit': {'validated_at': audit['validated_at'], 'build_exit': audit['build_exit'],
                                   'axiom_audit_exit': audit['axiom_audit_exit'], 'sha256': sha(audit_path)},
    'sealed_zip_unchanged': {'sha256': sha(zip_path), 'prior_package_manifest_sha256': sha(pack_path)},
    'local_links_checked': len(links), 'links': links,
    'claim_anchors': claim_sources,
    'history_sha256': {p: sha(R/p) for p in histories},
    'artifact_sha256': artifacts,
    'examples': toy,
    'teaching_reuse_actual_audit': reuse,
    'undergraduate_reader_simulation': {
        'reviewer': reader['reviewer'],
        'status': reader['status'],
        'unresolved_blockers': reader['unresolved_blockers'],
        'scope_limit': reader['scope_limit'],
        'reviewed_files': len(reviewed),
        'review_record_sha256': sha(reader_path),
        'is_actual_human_test': False,
    },
    'editing': ['pass 1: source and dated-history fidelity',
                'pass 2: reader sequence, concrete examples and figure inspection',
                'pass 3: claim scope, edge conditions and final link/fingerprint validation'],
    'manual_semantic_review': 'root author compared displayed formulae with linked sources; not independent expert review',
    'visual_review': 'four rendered PNGs inspected using view_image before deployment; fourth is conditional geometry, not a trajectory',
    'remaining': ['full proof tutorial', 'method-specific literature comparison', 'second substantive Lean application'],
}
(HERE/'validation.json').write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps({'status': record['status'], 'sources': len(expected_set), 'links': len(links),
                  'figures': len(toy['figures']), 'artifact_files': len(artifacts)}, ensure_ascii=True))
