# 当前形式化对应与可信边界

目标为原无限二维同步四邻 Maj-Random-If-Equal 最坏扩展期望恢复时间 τ(N)=Θ(N²)。**完整主定理尚未完成。**

分析167个证明模块、2282条辅助定理、168份分析源；核心125条定理及1模型、8源未变。合计176份正式源、2407条辅助定理与1个模型。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-21T00:41:11.681025+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，未冒称本次重编。

| 内容 | 主要模块 | 当前边界 |
|---|---|---|
| 原无限同步模型、真实随机law、含∞首达 | InfiniteGridModel、SquareGridLaw、InfiniteGridRecoveryTime | 原四邻规则、背景、边界、time尺度保持 |
| 原尺寸、exact-N最坏扩展期望 | PerturbationGeometry、OriginalRecoveryProfile | profile和最大值已定义/对应；一般有限与二次界未证 |
| 真时钟任务、rank、PW/零温、两向clock比较 | ClockReadiness、ActualClockTail、ClockRankTail、SquarePWCensoring、ZeroTemperature、ClockRecoveryComparison | 工具/比较已证，不代替CMST/FSS核心尾 |
| 同步重启和块尾 | FairMarksPastFuture、SquareRandomRestart | 真past/future law及乘法尾；二次尺度q<1未证 |
| strict-majority清理与实际改造字 | FiniteMajorityPeeling、GridMajorityPeeling、DropletModifiedWord | 终止、最大稳定core、次序无关、实际更新共轭已证 |
| 实际D∪外四邻保护域、字与clock law | ClippedProtectedGeometry、DropletStoppedWord、DropletStoppedClockLaw | 永久first loss冻结、原消失概率比较、真law已证 |
| 一般真实连续轮廓与原Good | OrthogonalBoundary系列、OrthogonalPhysicalContour、ProtectedGeometricGood | 全frontier、简单闭curve、全分割Euclidean弧长和原Good；严格<exit才Good |
| 真实物理exit与二次面积 | FrozenPhysicalExit、ProtectedExitArea | ENNReal含∞、finite attained/freeze、exit后缺失面积≥L²/1600 |
| joint历史、适应/渐进可测状态 | MarkedClockFiltration、MarkedHistoryWords、ObservedFrozenProcess、ObservedProgressive | 真实past可测版本、AE同原过程；未把旧global-guarded word逐样本适应当已证 |
| 原F退出停时版本 | LocalObservedHistory | 有限site全sample右gap、invalid独立flag、原F停时及AE真实物理law/扩展mean |
| marked-history停时后残余等待 | MarkedStoppedResidual、ProtectedExitResidual | single-site Exp(1)与停止σ独立；实际exit∧T真正finite实例；非完整未来vector/未来mark law |
| 正确面积势与有限率代数 | MaskedAreaGenerator、ProtectedAreaPotential | mask支持、D-relative面积有界可积、精确被禁birth修正；非物理补偿 |
| 未揭示marks fresh、物理补偿、CMST/FSS | 尚无完整闭合模块 | 当前主缺口，不能以这些结论作最终参数 |
| τ(N)=Θ(N²) | 尚未验收 | 不宣称完成，不按定理条数估完成百分比 |

[停时阶段](PROGRESS_2026-10-21_MARKED_STOPPING.md) · [面积阶段](PROGRESS_2026-10-21_AREA_POTENTIAL.md) · [下一阶段](../README.md)。旧PROGRESS文件按日期保留历史语境；当前状态以本文和最新统一audit为准。独立AI不是人类专家认证。
