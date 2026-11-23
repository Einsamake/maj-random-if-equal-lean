# Formalization map

[中文](FORMALIZATION_MAP.zh-CN.md) · [Formalization and audits](README.md)

The final theorem concerns the original synchronous process on the infinite square lattice. Finite squares and continuous-time clocks appear in intermediate comparisons. The geometric drift estimate, the key probability bounds and the comparison with synchronous rounds are proved within the development.

| Mathematical object or argument | Main Lean modules |
| --- | --- |
| Infinite four-neighbour rule, independent fair tie bits and a first hitting time that can be infinite | [InfiniteGridModel](analysis/MathResearchAnalysis/InfiniteGridModel.lean) · [SquareGridLaw](analysis/MathResearchAnalysis/SquareGridLaw.lean) · [InfiniteGridRecoveryTime](analysis/MathResearchAnalysis/InfiniteGridRecoveryTime.lean) |
| Enclosing-square size up to translation, the worst extended expectation at exact size and attainment of the maximum | [PerturbationGeometry](analysis/MathResearchAnalysis/PerturbationGeometry.lean) · [OriginalRecoveryProfile](analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean) |
| Cleanup deletions, the protected region and freezing on its first loss | [FiniteMajorityPeeling](analysis/MathResearchAnalysis/FiniteMajorityPeeling.lean) · [ClippedProtectedGeometry](analysis/MathResearchAnalysis/ClippedProtectedGeometry.lean) · [DropletStoppedClockLaw](analysis/MathResearchAnalysis/DropletStoppedClockLaw.lean) |
| Observed clock history, waiting times after stopping and compensation for individual events | [MarkedClockFiltration](analysis/MathResearchAnalysis/MarkedClockFiltration.lean) · [MarkedStoppedResidual](analysis/MathResearchAnalysis/MarkedStoppedResidual.lean) · [MarkedPredictableCompensation](analysis/MathResearchAnalysis/MarkedPredictableCompensation.lean) |
| Zero-weight boundary layer, weighted area, drift and the original synchronous lower bound | [ForbiddenBirthControl](analysis/MathResearchAnalysis/ForbiddenBirthControl.lean) · [PhysicalWeightedDrift](analysis/MathResearchAnalysis/PhysicalWeightedDrift.lean) · [OriginalQuadraticLower](analysis/MathResearchAnalysis/OriginalQuadraticLower.lean) |
| Staircase boundaries and their ordered-particle encoding, moment equations under the clock law, and covariance | [YoungParticles](analysis/MathResearchAnalysis/YoungParticles.lean) · [MixedClockDynkin](analysis/MathResearchAnalysis/MixedClockDynkin.lean) · [MixedClockCovariance](analysis/MathResearchAnalysis/MixedClockCovariance.lean) |
| Heat decay, clearing a local square and comparison with the clock process on the original square | [MixedClearingProbability](analysis/MathResearchAnalysis/MixedClearingProbability.lean) · [CrossSquareClockBound](analysis/MathResearchAnalysis/CrossSquareClockBound.lean) · [ClockRecoveryComparison](analysis/MathResearchAnalysis/ClockRecoveryComparison.lean) |
| Restart under the original synchronous law, extended tail sums and the quadratic upper bound | [SquareRandomRestart](analysis/MathResearchAnalysis/SquareRandomRestart.lean) · [ExtendedBlockTail](analysis/MathResearchAnalysis/ExtendedBlockTail.lean) · [OriginalQuadraticUpper](analysis/MathResearchAnalysis/OriginalQuadraticUpper.lean) |
| Quadratic order for the original worst expected recovery profile | [OriginalQuadraticRecovery](analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) |

The [proof guide](../docs/PROOF_GUIDE.md) explains how these arguments give the two bounds. The [final progress note (Chinese)](PROGRESS_2026-10-26_MAIN_THEOREM.md) and the [axiom and source audit](audit/original-theta-independent-final-binding-evidence.json) identify the checked version. Earlier records on stopped histories and compensation remain available through the [archival record](../docs/ARCHIVAL_RECORD.md).
