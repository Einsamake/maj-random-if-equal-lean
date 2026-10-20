# 实际掩膜面积率与正确势函数

MaskedAreaGenerator及ProtectedAreaPotential共24定理/28命名声明。

frozenGenerator直接用实际stoppedStep、每mask格点rate1及两个fair marks的1/2平均定义有限率代数。保护已缺失时为0；保护仍在时，负当前cardinality的率恰是rawAreaRate+cleanupRate。raw rate按mask内occupied低度/degree2死亡与vacant高度/degree2出生精确计数。cleanup额外删除由真实subset及Nat差合法转Real，非负。

若S⊆D⊆E，rawAreaRate(D,S)=rawAreaRate(E,S)+∑_{v∈E\D}birthIntensity(S,v)，最后一项非负，显式保留被mask禁止的出生。不能套用全平面恒漂移2代替这个式子，也未证明这个边界项累计有二次所需上界。

所有样本的stoppedWord及可测状态代表真正保持mask支持；因此实际D-relative面积|D\state|=|D|-|state|。generator常量移位与support使该面积率严格等于负card率；没有把generic |initialS\state|在D\initialS可能出生时错误识别。面积0≤area≤|D|，真实measure下可积；这不意味着恢复时间期望有限。

分析167个证明模块、2282条辅助定理、168份分析源；核心125条定理及1模型、8源未变。合计176份正式源、2407条辅助定理与1个模型。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-21T00:41:11.681025+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，未冒称本次重编。

[率代数专项](audit/masked-area-generator-stage-declarations-validation.json) · [势函数专项](audit/protected-probability-stage-declarations-validation.json) · [独立审查](audit/masked-area-generator-independent-review.md) · [势函数审查](audit/protected-probability-independent-review.md)。仍需实际marked clock计数/补偿、mask项控制及CMST/FSS概率。
