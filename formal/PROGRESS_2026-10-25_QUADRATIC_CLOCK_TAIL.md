# 实际加权线性率与平方时间概率界

完整原同步τ(N)=Θ(N²)仍未完成。本阶段给真正原CLOCK方框初态的二次时间概率下尾接口，没有做同步时间转换或二次上界。

## 无核心概率输入的严格结果

WeightedRawRate对L≥2、实际Shape、innerDiamond包含和clipped支持，证明2·rawWeightedRate等于四种实际镜像的NW charge之和。稳定性与真实受保护凸性排除对向degree2死亡，空点行列凸性排除对向出生及degree>2；32种局部情形与有限反射换元均已实际证明。四个NW界合并得到raw≤2(L+2)+2perimeter。投影基数各≤2L+1给真实perimeter≤8L+4，因此raw≤18L+12，没有以raw界或perimeter界作输入。

PhysicalWeightedDrift将actual strictword的Shape接到共同AE全时刻beforeState；active冻结条件给真实inner保护，失守后raw=0。先证明样本及时间均值可积，再用真实Lebesgue时间长度积分，得到

E[W_T] ≤ (18L+12)T + (L+2)(4L+2)。

取K=12288000、L≥K、T=L²/K，实际加权失守门槛为L³/128000；代数给均值≤L³/256000，因此真实P(auxiliary exit≤T)≤1/2。正确原过程比较同时给P(original CLOCK full-square extinction by T)≤1/2。未假设无界退出时间有限，∞保留；原clock方框边长2L+1，原有限模型参数2L−1，不能把L直接称原尺寸N或把clock时间叫同步轮数。

## 验收与范围

分析208个证明模块、2800条辅助定理、209份分析源；核心125条定理及1模型、8源未变。合计217份正式源、2925条辅助定理与1个模型，完整公理输出2926项。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-25T05:12:24.607031+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，本次未重编核心。

本批2模块25theorem/29named（15+14）均actualbuild0/标准trust0专项审计0。此前215源批122新theorem/142named及210源批58新theorem/72named都保存独立历史；旧JSON/log/table/入口完整归档before-weighted-area-stage和before-weighted-raw-bound，不能用旧审计覆盖新源。

[独立语义审查](audit/weighted-raw-physical-independent-review.md) · [最终217绑定](audit/physical-weighted-independent-final-binding-evidence.json) · [统一验证](audit/analysis-validation.json)。独立AI核全部217源/2926真实输出；语义范围明确排除其自写的NW依赖，不冒称人类专家认证。无sorry/admit、自定义公理、unsafe、native_decide或内核绕过。

## 下一完整阶段

从SquareGridLaw.two_way_clock_tail的第一方向直接把clock慢接到原无限同步恢复尾，不重做scan、wholelaw或尺寸定义。使用SchedulingFailure.time≤L²/K及已证一般时间均值界，可避免再开clock CDF单调证明。再用真实有限支持比较处理较小奇数方岛到原任意N，ExtendedRecoveryExpectation尾界给含∞的期望下界，OriginalRecoveryProfile.square_expectedRecovery_le_tau供最坏原exact-N量词。所有数值步和参数对齐仍待Lean证明；二次上界及自含FSS核心另一路尚未完成。

[下一阶段具体接口与数值待证步](../research/followup/NEXT_SYNC_LOWER_ROUTE_2026-10-25.md) · [真正物理概率源码](analysis/MathResearchAnalysis/PhysicalWeightedDrift.lean) · [四方向raw率源码](analysis/MathResearchAnalysis/WeightedRawRate.lean)。
