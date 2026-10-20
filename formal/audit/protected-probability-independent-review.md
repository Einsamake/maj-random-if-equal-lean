# 实际截断退出残余与支持正确的面积势：独立AI复核

2026-10-21，代理`/root/history_audit_1021`。只读冻结正式ProtectedExitResidual、ProtectedAreaPotential及已审所用接口和实际审计日志。没有编辑Lean、运行构建或派代理，不是人类专家或数学新颖性认证。

## 专项状态

ProtectedExitResidual 9theorem/10named，SHA256 `76e1446753e684463fda762ff19dfa9709b302e2bbec5b5717335bfb5c5ec236`；ProtectedAreaPotential 11theorem/11named，SHA256 `dff8b3573f48a230d7d846b19de383d6a109d349d1f390cd2e851c127b6db7d2`。合计20条theorem/21named，源码字节与[专项JSON](protected-probability-stage-declarations-validation.json)匹配；声明表与[21项公理输出](protected-probability-stage-declarations-axioms.log)逐项顺序相同。

2026-10-21T00:40:32.718686+08:00，专项[真实build](protected-probability-stage-declarations-build.log)及standard Lean --trust=0审计均exit0，只三标准公理，零新Lean warning。**精确语义、专项及最终统一证据通过（最终绑定见文末）。**

## 截断之后才转有限Real

boundedExit先在ENNReal中取min(LocalObservedHistory.exit,T)，其中T为NNReal有限时限，再toReal并嵌入WithTop Real。capped_exit_ne_top明确由min≤T与T≠∞给出点态有限；因此unbounded exit=∞时，min为T，输出T，不会因∞.toReal=0错误改成0。T=0时截断为0，是正确的零时限。

boundedExit_nonnegative、boundedExit_ne_top及≤T均点态证明，不以原退出AEfinite或任何待证概率尾作输入。boundedExit_isStoppingTime在原Real joint F逐阈值证明：r<0时事件空；r≥0时，有限cap的toReal≤r等价于exit≤ofReal(r)或T≤ofReal(r)，后者成立则全空间，否则精确为原F_r可测absorbingLoss(r)。证明中toReal顺序等价同时使用cap与ofReal(r)的有限性，未错误把ENNReal∞顺序压到Real。

## 真实物理cap实例与残余独立

共同Good样本上LocalObservedHistory.exit=physicalExit，所以新boundedExit与真实物理min(physicalExit,T)逐样本相同，进而在原真实clock×marks law下AE相同，∞保留为有限截断T。这里使用已证完整过程AE识别，不假定原物理首达代表逐样本对未完备F停时。

boundedExit_wait_hasLaw及boundedExit_wait_independent_stopped_history实际代入此R：IsStoppingTime、nonnegative、ne_top都由本模块无条件证明，AE有限性来自pointwise ne_top，**没有把未证的unbounded physicalExit有限性当参数**。得到每个site在这个真正有界停止时刻之后的Exp(1)残余和与其原joint停止σ代数独立。仍没有泛称多site residual向量独立、未来marks fresh或完整strongMarkov。

## 全样本支持与正确的缺失面积势

stoppedStep_supported由真实modifiedStep mask支持和freeze分支得到；stoppedWord_supported按实际递归执行归纳。observed_state_supported分别处理存在唯一graph的确定性执行结果和无graph时的实际initial S fallback，均在S⊆D下证明state⊆D，对全部样本成立，而非仅AE。

missing_area_eq_negative_card先用支持得到card(D\S)+card(S)=card(D)，再转Real，避免Nat截零造成代数误判。observed_area_eq_negative_card只在对应已证state支持下使用这条等式。

missing_area_generator的potential明确是|D\T|，不是一般initial S相对缺失面积。frozenGenerator_congr只要求两个potential在当前S及真实两mark单步结果上相同；stoppedStep_supported保证这些点均含于D。再用已证明constant shift不变性，才把|D\T|的有限率化为-|T|，接真实raw+cleanup/freeze分解。此前指出的generic initial S与mask D混淆在这段中已准确修复。

## 面积可积不是恢复时间可积

observed_area_measurable从真实history可测版本提升ambient，0≤|D\state|≤card(D)是点态有限集合差界。实际clock×marks为概率measure，因此该Real面积在每个固定t可积。这只保证面积observable可用，不推出unbounded exit有限、其期望有限或任何N²时间界。

本模块只建立有限更新率代数和实际有界停时残余实例，没有证明原物理clock下的Dynkin、martingale补偿、面积时间积分等式或自含CMST/FSS尾。完整原τ(N)=Θ(N²)仍未证明；独立AI不冒充人类专家认证。


## 最终统一证据绑定（2026-10-21）

实际统一时间2026-10-21T00:41:11.681025+08:00，2282分析辅助定理/168分析源，统一build_exit=axiom_audit_exit=0、kernel_trust_level=0。独立代理核当前168分析+8既有核心=176正式源的集合与逐字节SHA全部精确匹配，所审四个新模块的正式指纹同时匹配专项与全局记录。完整2282分析、126核心公理输出与#print表逐名、逐顺序相同，含声明名内撇号，均只标准三公理或无公理，无占位公理。

LocalObservedHistory21/24、MarkedStoppedResidual8/9、ProtectedExitResidual9/10、ProtectedAreaPotential11/11，共49条新增theorem/54named，两个专项33+21均实际build/audit0、standardtrust0，零新Lean warning。当前合计2407条辅助定理及1模型、2408项全局公理输出。核心8源与既有验收相同，没有声称本次重编核心；既有batteries文档修改warning保留。独立代理没有重新语义审阅所有旧模块或运行Lean。

此前写入时的待统一状态现已由实际证据闭合。后续UnrevealedMarkInvariance仍为草稿，不在本次2282/176验收内。已完成的是本报告精确接口，物理生成元/补偿、未来fresh marks等核心连接、自含CMST/FSS与原τ(N)=Θ(N²)主定理仍须继续；独立AI不等于人类专家认证。
