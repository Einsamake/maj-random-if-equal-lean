"""Package project proofs and audit evidence, without tools or dependency caches."""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / 'formal'
checked_sources = 0
for name, base in [('core-validation.json', FORMAL),
                   ('analysis-validation.json', FORMAL / 'analysis')]:
    validation = json.loads((FORMAL / 'audit' / name).read_text(encoding='utf8'))
    assert validation['build_exit'] == validation['axiom_audit_exit'] == 0
    module_dir = 'MathResearch' if base == FORMAL else 'MathResearchAnalysis'
    actual_sources = set((base / module_dir).glob('*.lean')) | {base / f'{module_dir}.lean'}
    validated_sources = {base / source_name for source_name in validation['source_sha256']}
    assert actual_sources == validated_sources, 'Project source set changed: run the full validator first'
    for source_name, expected in validation['source_sha256'].items():
        assert hashlib.sha256((base / source_name).read_bytes()).hexdigest() == expected
        checked_sources += 1
paths = [ROOT / name for name in ['docs/PROOF_GUIDE.md', 'docs/render_clock_timeline.py', 'docs/VERIFICATION.md', 'README.md', 'HANDOFF.md', 'STATUS.md',
    '阶段性成果_2026-10-14.md',
    '复盘与后续路线_2026-10-14.md', 'archive/README.md',
    '工作区整理与工具研究_2026-10-16.md', 'archive/cleanup-2026-10-16.json',
    'archive/disk-inventory-2026-10-16.json',
    '形式化独立核查_2026-10-14.md',
    'archive/organization-2026-10-14.json', 'deliverables/README.md',
    'research/followup/ca_clean_proof.md', 'research/followup/METHOD_LEDGER_2026-10-18.md', 'research/followup/METHOD_LEDGER_2026-10-19.md', 'research/followup/METHOD_LEDGER_2026-10-20.md', 'research/followup/METHOD_LEDGER_2026-10-21.md', 'research/followup/METHOD_LEDGER_2026-10-22.md', 'research/followup/METHOD_LEDGER_2026-10-23.md', 'research/followup/METHOD_LEDGER_2026-10-24.md', 'research/followup/METHOD_LEDGER_2026-10-25.md', 'research/followup/NEXT_SYNC_LOWER_ROUTE_2026-10-25.md', 'research/followup/novelty_review.md',
    'research/followup/public_resolution_check_2026-10-14.md',
    'research/followup/PROGRESS_ESTIMATE_2026-10-14.md',
    'research/followup/REVIEW_DIRECTION_2026-10-14.md',
    'research/followup/CLEANUP_AUDIT_2026-10-14.md']]
paths += [ROOT/'docs/render_explainer.py']
paths += sorted(p for p in (ROOT/'docs/images').iterdir() if p.is_file())
paths += sorted(path for path in (ROOT / 'reports' / 'initial-research').iterdir()
                if path.is_file())
paths += sorted(path for path in (ROOT / 'scripts').iterdir()
                if path.is_file() and path.suffix in {'.py', '.ps1'})
for directory in ['MathResearch', 'analysis/MathResearchAnalysis', 'scripts']:
    paths += sorted(path for path in (FORMAL / directory).iterdir()
                    if path.is_file() and path.suffix in {'.lean', '.md', '.py'})
for name in ['MathResearch.lean', 'lakefile.toml', 'lean-toolchain',
    'analysis/MathResearchAnalysis.lean', 'analysis/lakefile.toml',
    'analysis/lean-toolchain', 'analysis/lake-manifest.json', 'analysis/AnalysisAxioms.lean',
    'analysis/TaskPathsAudit.lean',
    'FORMALIZATION_MAP.md', 'LEAN_README.md', 'PROGRESS_2026-10-13.md',
    'PROGRESS_2026-10-13_CLOCKS.md', 'PROGRESS_2026-10-13_READINESS.md',
    'PROGRESS_2026-10-14_STOPPED_CLOCKS.md',
    'PROGRESS_2026-10-14_WORDS.md',
    'PROGRESS_2026-10-14_PW.md',
    'PROGRESS_2026-10-14_COMPARISON.md',
    'PROGRESS_2026-10-14_RANDOM_RECOVERY.md',
    'PROGRESS_2026-10-15_GRID.md',
    'PROGRESS_2026-10-15_ORIGINAL_STATEMENT.md', 'CMST_DEPENDENCY_PLAN.md',
    'PROGRESS_2026-10-15_MAJORITY_PEELING.md', 'PROGRESS_2026-10-16_CLIPPED_DROPLET.md', 'PROGRESS_2026-10-16_MODIFIED_CLOCK.md', 'PROGRESS_2026-10-16_PROTECTED_DOMAIN.md', 'PROGRESS_2026-10-17_CONTOUR_FOUNDATION.md',
    'PROGRESS_2026-10-17_GEOMETRIC_CONTOUR.md', 'PROGRESS_2026-10-17_LOCAL_UPDATE.md', 'PROGRESS_2026-10-18_PROTECTED_EVOLUTION.md', 'PROGRESS_2026-10-18_ORTHOGONAL_BOX.md', 'PROGRESS_2026-10-19_GENERAL_CONTOUR.md', 'PROGRESS_2026-10-19_STOPPED_CLOCK.md', 'PROGRESS_2026-10-19_TIME_CONSISTENCY.md', 'PROGRESS_2026-10-19_PHYSICAL_EXIT.md', 'CHECKPOINT.md',
    'NEXT_STOPPED_WAIT.md', 'NEXT_PHASE.md', 'FINITE_PW_CONTRACT.md',
    'INFINITE_GRID_CONTRACT.md', 'ORIGINAL_STATEMENT_CONTRACT.md']:
    paths.append(FORMAL / name)
for name in ['core-validation.json', 'core-build.log', 'core-axioms.log', 'CoreAxioms.lean',
    'analysis-validation.json', 'analysis-build.log', 'analysis-axioms.log',
    'poisson-interface-audit.json', 'task-path-semantic-review.md', 'concrete-clock-review.md',
                'readiness-clock-review.md', 'stopped-clock-review.md',
                'square-pw-review.md', 'infinite-grid-semantic-review.md',
                'infinite-grid-semantic-validation.json']:
    paths.append(FORMAL / 'audit' / name)
paths += sorted(path for path in (FORMAL / 'audit' / 'history').rglob('*') if path.is_file())
paths += sorted(path for path in (ROOT / 'archive' / 'docs').rglob('*') if path.is_file())
if (FORMAL / 'audit' / 'workspace-validation.json').is_file():
    paths.append(FORMAL / 'audit' / 'workspace-validation.json')
stage_audits = set()
for pattern in ['clock-rank-tail-*', 'rank-slot-embedding-*', 'clock-marks-*',
                'square-attractivity-*', 'SquareAttractivityAxioms.lean',
                'rank-scan-embedding-*', 'RankScanEmbeddingAxioms.lean',
                'scan-kernel-*', 'SquareScanKernelAxioms.lean',
                'extended-recovery-time-*', 'ExtendedRecoveryTimeAxioms.lean',
                'scan-order-*', 'square-random-recovery-review.md',
                'square-random-recovery-validation.json',
                'infinite-grid-*', 'square-grid-*', 'SquareGridEmbeddingAxioms.lean',
                'fair-marks-transport-*', 'recovery-time-transport-*',
                'fair-marks-past-future-*', 'square-deterministic-restart-*',
                'square-random-restart-*',
                'perturbation-geometry-*', 'PerturbationGeometryAxioms.lean',
                'perturbation-normalization-*', 'extended-recovery-expectation-*',
                'ExtendedRecoveryExpectationAxioms.lean',
                'SmallDiameterRecoveryAxioms.lean', 'small-diameter-recovery-*',
                'original-statement-semantic-*', 'original-statement-independent-evidence.json',
                'finite-majority-peeling-*', 'majority-peeling-*',
                'clipped-diamond-geometry-*', 'droplet-modified-word-*', 'clipped-droplet-*',
                'automation-removal.json', 'wake-0505-verification.json',
                'grid-cell-boundary-*', 'clipped-orthogonal-sections-*',
                'clipped-boundary-*', 'grid-boundary-*', 'clipped-grid-connectivity-*',
                'orthogonal-grid-convexity-*', 'contour-foundation-*', 'stopped-clock-*', 'droplet-stopped-*', 'unrevealed-mark-*', 'stopped-mark-slices-*', 'stopped-fresh-mark-*', 'marked-residual-pair-*', 'clock-arrival-count-tail-*', 'marked-ring-count-*', 'marked-ring-integrability-*', 'truncated-exponential-*', 'clock-gap-occupation-*', 'clock-ring-mean-*', 'marked-ring-mean-*', 'clock-interval-history-*', 'clock-interval-count-*', 'marked-interval-factor-*', 'marked-conditional-count-*', 'conditional-clock-*', 'marked-clock-point-measure-*', 'marked-point-measure-*', 'marked-predictable-rectangles-*', 'predictable-clock-reference-*', 'predictable-clock-sigma-*', 'marked-predictable-compensation-*', 'predictable-compensation-*', 'observed-pre-state-*', 'strict-clock-prefix-*', 'actual-pre-state-*', 'predictable-area-contribution-*', 'actual-area-telescope-*', 'real-predictable-compensation-*', 'marked-area-sum-*', 'actual-area-dynkin-*', 'physical-area-generator-*', 'physical-area-tail-*', 'forbidden-birth-*', 'weighted-area-*', 'weighted-exit-*', 'weighted-raw-*', 'physical-weighted-*', 'sync-lower-*', 'mixed-square-*', 'young-*', 'exclusion-*', 'cumulative-cleanup-*', 'clock-time-illustration-*', 'future-gap-history-*', 'marked-clock-filtration-*', 'marked-history-words-*', 'observed-stopping-*', 'observed-frozen-*', 'observed-progressive-*', 'masked-area-generator-*', 'marked-deterministic-residual-*', 'marked-residual-stage-*', 'local-history-exit-*', 'protected-probability-*', 'protected-area-potential-*', 'protected-exit-residual-*', 'frozen-physical-exit-*', 'clock-word-consistency-*', 'orthogonal-boundary-*', 'orthogonal-physical-contour-*', 'protected-geometric-good-*', 'region-*', 'update-stage-*', 'protected-column-*', 'protected-corner-*', 'protected-stage-*', 'exit-area-stage-*', 'vacant-quadrant-*', 'orthogonal-perimeter-*', 'orthogonal-physical-box-*', 'orthogonal-box-stage-*', 'grid-region-connectivity-*', 'github-private-repository.json', 'github-snapshot-validation.json', 'convex-birth-update-*', 'grid-perimeter-update-*', 'grid-perimeter-dynamics-*', 'cleanup-connectivity-*', 'convex-local-update-*',
                'grid-cell-region-*', 'grid-physical-region-*', 'grid-contour-length-*',
                'clipped-region-box-*', 'clipped-physical-box-*', 'clipped-initial-contour-*',
                'geometric-contour-*', 'wake-0505-*',
                'clipped-protected-geometry-*', 'protected-domain-*',
                'centered-peeling-transport-*', 'droplet-domain-comparison-*',
                'droplet-clock-law-*', 'whole-square-clock-*', 'modified-clock-*',
                'independent-semantic-*', 'IndependentSemanticKernelAudit.lean',
                'independent_semantic_checks.py',
                'clock-execution-law-*', 'clock-selected-marks-*',
                'finite-word-kernel-*', 'marked-event-trace-*', 'square-gibbs-*',
                'ClockRankTailAxioms.lean', 'RankSlotEmbeddingAxioms.lean',
                'ClockMarksIndependentAxioms.lean', 'ClockExecutionLawAxioms.lean',
                'ClockSelectedMarksAxioms.lean', 'FiniteWordKernelAxioms.lean',
                'MarkedEventTraceAxioms.lean', 'SquareGibbsAxioms.lean',
                'SquareGibbsLawAxioms.lean']:
    stage_audits.update(path for path in (FORMAL / 'audit').glob(pattern) if path.is_file())
paths += sorted(stage_audits - set(paths))
paths += sorted(path for path in (FORMAL / "drafts").rglob("*") if path.is_file())
paths += [p for p in sorted(FORMAL.glob('PROGRESS_2026-10-2*.md')) if p not in paths]
assert len(paths) == len(set(paths))
assert all(path.is_file() for path in paths)
manifest = {path.relative_to(ROOT).as_posix(): {
    'bytes': path.stat().st_size,
    'sha256': hashlib.sha256(path.read_bytes()).hexdigest()
} for path in paths}
manifest_path = FORMAL / 'LEAN_MANIFEST.json'
manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding='utf8')
paths.append(manifest_path)
output = ROOT / 'deliverables' / 'Lean形式化材料_2026-10-25.zip'
output.parent.mkdir(exist_ok=True)
with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
    for path in paths:
        name = path.relative_to(ROOT).as_posix()
        assert not ({'.tools', '.lake', '.git'} & set(Path(name).parts))
        archive.write(path, name)
with zipfile.ZipFile(output) as archive:
    assert archive.testzip() is None
    assert len(archive.namelist()) == len(paths)
    for name, record in manifest.items():
        content = archive.read(name)
        assert len(content) == record['bytes']
        assert hashlib.sha256(content).hexdigest() == record['sha256']
record = {'files': len(paths), 'zip_bytes': output.stat().st_size,
    'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
    'validated_sources_matched': checked_sources, 'checks_passed': True}
(FORMAL / 'audit' / 'package-validation.json').write_text(
    json.dumps(record, ensure_ascii=False, indent=2), encoding='utf8')
output.with_suffix('.zip.sha256').write_text(
    record['sha256'] + '  ' + output.name + '\n', encoding='utf8')
print(json.dumps(record, ensure_ascii=False))
