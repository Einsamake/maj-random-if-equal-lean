# 原共同历史中的退出停时与真实残余等待

MarkedDeterministicResidual、LocalObservedHistory、MarkedStoppedResidual、ProtectedExitResidual四模块共45定理/51命名声明。

有限个实际格点、逐arrival-index单调的clipped gap部分和，保证每个样本/实t均存在严格右侧无新事件间隙，完全不依赖global Good(t+1)。未来完整finite fiber过滤给过去完整fiber，真实mark字按时间前缀一致。invalid-history补集是持久可测事件；将其作为独立cemetery flag并与合法历史frozen loss合并，得到逐样本单调/右局部常值的absorbingLoss。其firstLossTime在原nnHistory即为停时，阈值事件逐样本精确。

在共同AE全时Good样本，cemetery永不触发，新退出等于原physicalExit，含∞law和扩展期望相同。I=∅等边界仍成立，不把invalid flag当实际state-missing。

固定整场marks η后，joint历史及其全历史iSup的section映回纯clock历史；marked停时和停止σ事件的section是真正clock停时及停止σ事件。实际乘积measure的AE Fubini将已证clock stopped residual law运输回来，允许R依赖已揭示marks，只要求非负且AE finite。这里只证明single-site Exp(1)与完整停时历史独立，未证明多site residual向量或未来marks fresh。

实际退出在ENNReal中先与有限T取min，证明结果finite后才toReal：原退出∞映成T。得到原Real jointF中的非负pointwise finite停时，直接实例化上述law，无原physicalExit有限性输入。

分析167个证明模块、2282条辅助定理、168份分析源；核心125条定理及1模型、8源未变。合计176份正式源、2407条辅助定理与1个模型。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-21T00:41:11.681025+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，未冒称本次重编。

[一般原F停时/残余专项](audit/local-history-exit-stage-declarations-validation.json) · [实际截断专项](audit/protected-probability-stage-declarations-validation.json) · [语义审查](audit/local-history-exit-independent-review.md) · [实际实例语义审查](audit/protected-probability-independent-review.md)。CMST/FSS及最终二次界仍缺。
