# 共同历史与可测冻结过程

MarkedClockFiltration、MarkedHistoryWords、RationalProtectedExit、ObservedFrozenProcess、ObservedProgressive五模块共69定理/86命名声明。原joint历史只含到时arrival和已揭示identity marks，未加入global Good或future全场。

截断到时与有限完整字/mark-vector fiber真正历史可测；coverage、严格时间序和真实identity marks给完整状态的唯一可数graph。选择唯一graph状态、无合法完整历史时退回初态，得到逐样本适应和渐进可测版本；同一AE样本∀real t等于原stateAt。受限time×sample可测证明明确包含horizon端点的arrival≤T条件；不能只比较min(arrival,T)≤s。

Real缺失面积强渐进可测，stoppedValue在退出停时σ代数可测。∞时stoppedValue的untopA只给任意时刻fallback；物理退出面积识别只在finite guard下成立。原退出本身保留ENNReal∞，未证明其有限。

RationalProtectedExit给右连续化F₊停时及真实AE物理law/lintegral。后来[原历史停时](PROGRESS_2026-10-21_MARKED_STOPPING.md)进一步给原F版本；没有证明F=F₊。

分析167个证明模块、2282条辅助定理、168份分析源；核心125条定理及1模型、8源未变。合计176份正式源、2407条辅助定理与1个模型。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-21T00:41:11.681025+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，未冒称本次重编。

专项与独立AI证据：[filtration](audit/marked-clock-filtration-stage-declarations-validation.json)、[finite loss/stopping](audit/observed-stopping-stage-declarations-validation.json)、[complete state](audit/observed-frozen-stage-declarations-validation.json)、[progressive](audit/observed-progressive-stage-declarations-validation.json)、[语义核对](audit/observed-progressive-independent-review.md)。没有据此宣称主定理完成。
