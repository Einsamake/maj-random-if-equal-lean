# Region frontier continuation handoff

Updated 2026-10-17 05:20, Asia/Shanghai.
Owner: /root/domain_exit_comparison.
Local status: completed and frozen; unified project acceptance is owned by root.

## Verified result

The completed formal source is:
formal/analysis/MathResearchAnalysis/GridRegionBoundary.lean

For every finite occupied set S it proves:
frontier (GridCellRegion.region S) =
  union over e in GridCellBoundary.boundary S of
    GridBoundarySegments.closedSegment e.

The upper inclusion was proved from actual open rectangles covering occupied
cell pairs or four-cell blocks, strict face/corner case analysis, and actual
outgoing exposed edges at mixed-occupancy corners. Entire real affine segments
are used, including endpoints. The lower inclusion is the already proved
GridCellRegion.boundarySegments_subset_frontier; no desired frontier equality,
Jordan or contour assumption is passed in.

Final public API:
- frontier_region_subset_boundarySegments S
- frontier_region_eq_boundarySegments S
- mem_frontier_region_iff S p

## Actual validation

Official lake build session 63446 finished exit 0 in 14 seconds, with no
source warnings. Audit session 78816 finished exit 0 for all 18 public
theorems using standard Lean 4.35.0-rc4 --trust=0.
Only propext, Classical.choice and Quot.sound occur.
Source SHA256:
16e310f64230f382ce91742a30e343d12be9303a0f56a23435c5361f842ece5f

Evidence:
- formal/audit/region-boundary-build.log
- formal/audit/region-boundary-axioms.lean
- formal/audit/region-boundary-axioms.log
- formal/audit/region-boundary-validation.json

The completed draft was removed only after verifying that its SHA256 matched
the official source. No own build/audit process remains running, no unfinished
topology draft remains, and no old frozen source was edited.

## Remaining boundary

The region uses doubled spatial coordinates; the other agent's
GridPhysicalRegion module handles the genuine physical half-scale map.
This file does not prove Jordan, an invariant Good class, modified-process
preservation, area drift, CMST/FSS probability bounds, or the main CA theorem.
Those remain root's subsequent tasks.

The earlier OrthogonalGridConvexity subtask is also fully frozen and its
15-declaration trust-zero audit remains in orthogonal-grid-convexity-* evidence.
