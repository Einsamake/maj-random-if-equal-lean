# 形式化结构

主定理研究原无限格点同步过程，辅助有限方框与连续时钟仅用于比较。最终结论不以几何漂移界、核心概率界或同步—时钟比较作为外加前提。

| 数学对象或论证 | 主要模块 |
| --- | --- |
| 无限四邻规则、独立公平标记、允许无穷的首达时间 | [InfiniteGridModel](analysis/MathResearchAnalysis/InfiniteGridModel.lean)、[SquareGridLaw](analysis/MathResearchAnalysis/SquareGridLaw.lean)、[InfiniteGridRecoveryTime](analysis/MathResearchAnalysis/InfiniteGridRecoveryTime.lean) |
| 平移方形尺寸、恰尺寸最坏扩展期望及最大值实现 | [PerturbationGeometry](analysis/MathResearchAnalysis/PerturbationGeometry.lean)、[OriginalRecoveryProfile](analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean) |
| 清理、保护域与首次失守冻结 | [FiniteMajorityPeeling](analysis/MathResearchAnalysis/FiniteMajorityPeeling.lean)、[ClippedProtectedGeometry](analysis/MathResearchAnalysis/ClippedProtectedGeometry.lean)、[DropletStoppedClockLaw](analysis/MathResearchAnalysis/DropletStoppedClockLaw.lean) |
| 可观测历史、停止后等待与逐事件补偿 | [MarkedClockFiltration](analysis/MathResearchAnalysis/MarkedClockFiltration.lean)、[MarkedStoppedResidual](analysis/MathResearchAnalysis/MarkedStoppedResidual.lean)、[MarkedPredictableCompensation](analysis/MathResearchAnalysis/MarkedPredictableCompensation.lean) |
| 零权层、加权面积、漂移与原同步下界 | [ForbiddenBirthControl](analysis/MathResearchAnalysis/ForbiddenBirthControl.lean)、[PhysicalWeightedDrift](analysis/MathResearchAnalysis/PhysicalWeightedDrift.lean)、[OriginalQuadraticLower](analysis/MathResearchAnalysis/OriginalQuadraticLower.lean) |
| 阶梯形与有序粒子、真实矩方程及协方差 | [YoungParticles](analysis/MathResearchAnalysis/YoungParticles.lean)、[MixedClockDynkin](analysis/MathResearchAnalysis/MixedClockDynkin.lean)、[MixedClockCovariance](analysis/MathResearchAnalysis/MixedClockCovariance.lean) |
| 热衰减、局部清空与原尺寸时钟比较 | [MixedClearingProbability](analysis/MathResearchAnalysis/MixedClearingProbability.lean)、[CrossSquareClockBound](analysis/MathResearchAnalysis/CrossSquareClockBound.lean)、[ClockRecoveryComparison](analysis/MathResearchAnalysis/ClockRecoveryComparison.lean) |
| 原同步重启、扩展尾和与二次上界 | [SquareRandomRestart](analysis/MathResearchAnalysis/SquareRandomRestart.lean)、[ExtendedBlockTail](analysis/MathResearchAnalysis/ExtendedBlockTail.lean)、[OriginalQuadraticUpper](analysis/MathResearchAnalysis/OriginalQuadraticUpper.lean) |
| 原量词下的二次渐近结论 | [OriginalQuadraticRecovery](analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) |

[证明纲要](../docs/PROOF_GUIDE.md)按数学依赖组织两侧估计。[最终检查记录](PROGRESS_2026-10-26_MAIN_THEOREM.md)与[公理输出及源绑定](audit/original-theta-independent-final-binding-evidence.json)用于核对该版本；它们不将完整经典强尾定理或全未来向量的强 Markov 性列为最终外加输入。有关停止历史和局部补偿的较早记录按[归档约定](../docs/ARCHIVAL_RECORD.md)保存。
