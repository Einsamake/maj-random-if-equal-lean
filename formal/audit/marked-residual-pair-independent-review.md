# 单site残余等待与新标记联合分布：独立路线审查

当前仅路线审查通过，MarkedResidualPair新源码尚未出现；未核任何新增Lean构建或公理审计，不计入2321分析定理/179源的既有验收。独立AI核查不等于人类专家认证。

已逐原文核StoppedMarkSlices、StoppedFreshMark、MarkedStoppedResidual、SurvivalLaw与ProtectedExitResidual。对停止σ事件E及任意可测A⊆Real取G=E∩waiting⁻¹'A：G是ambient事件即可，不要求它属于停止σ；candidate_waiting_flip与candidate_stopped_event_flip_iff逐样本保持G。因此实际invariant_factor给每个Bool切片的half质量，可直接证明restrict G下nextMark的完整fair限制law，不需要再由阈值CDF唯一性扩展。

再用已证明waiting在restrict E下的Exp(1)限制law，得到任意Real×Bool可测矩形上的pair质量μ(E)·Exp(A)·fair(B)，Measure.ext_prod由有限左侧推前measure将矩形相等提升为完整pair推前相等。E=univ给真实pair HasLaw，其余停止事件给pair与停止σ独立。此路线直接证明联合factorization，没有由两个marginal独立偷推联合独立。

公平标记切片需要R几乎处处有限，不需要R非负；完整Exp×fair pairlaw另需R非负。R=∞或无未来arrival时的原total waiting/mark fallback仍保留，由AEfinite及实际cofinal clock在law层面排除；不得先把∞ readiness转0。实际boundedExit先ENNReal cap有限T再toReal，原退出∞时仍为T，故可实例化无需假设原退出有限。

范围始终为固定site v。该pair theorem即使成功，也不证明多site residual向量、完整future字段、first-global-ring race、实际物理补偿/Dynkin或CMST/FSS核心概率。主定理尚未完成。新增源码出现后须重读最终原文，绑定SHA与实际全命名声明standard trust0输出，最后核统一179+源exact set/hash后才更新验收状态。
