# 真正停时之后的下一site mark与联合等待因子化：独立AI复核

2026-10-21，代理`/root/history_audit_1021`。只读正式冻结StoppedFreshMark、已审候选切片/未揭示mark/残余law及实际审计日志，未改Lean、未构建或派新代理。不冒充人类专家或新颖性认证。

## 正式专项证据

StoppedFreshMark 18条theorem/19named（1def），含三个实际boundedExit实例。SHA256 `236863ed7900a27b3a8049b61bf37128989a6a016a356fb30f8fdd5475d166ff`，与[专项JSON](stopped-fresh-mark-stage-declarations-validation.json)逐字节匹配；声明表与[19项完整公理输出](stopped-fresh-mark-stage-declarations-axioms.log)逐名顺序相同。[实际build](stopped-fresh-mark-stage-declarations-build.log)与standard Lean --trust=0审计均exit0，只有标准三公理，零新Lean warning。时间2026-10-21T05:38:57.414994+08:00。

**精确语义、专项及最终统一证据通过（最终绑定见文末）。** 同时独立再核UnrevealedMarkInvariance9/12、StoppedMarkSlices12/13的最终SHA及完整专项输出，三模块共39条theorem/44named均匹配，未把旧176源验收冒充新模块统一证据。

## 总定义和fallback分支保留

nextMark不是抽象fresh coin，也不是假设随机选择与marks独立。它在实际样本上取满足R<arrival(v,k)的Nat.find最小identity index，返回同一真实mark z.2(v,k)；无未来ring时返回false。

candidate_find证明全部先前index已到R，candidate_unique将任何候选与实际Nat.find认同。nextMark_fiber精确保留“存在候选且该mark=b”或“无候选且false=b”两分支，nextMark_measurable由可数候选并与fallback补集证明ambient可测。特别b=false时没有漏掉无future样本；未在全样本上直接删除例外回退。

## 真正AE覆盖允许R依赖过去marks

candidate_exists_ae将既有真实clock cofinal概率一集合经实际product fst拉回；该集合给**∀real r存在future到时**，与R的AEfinite集合相交后，可以在每条样本自己的随机R处使用。这里没有把逐固定r的AE结论错误替换成随机r，也不要求R独立于marks。

candidate_partition_tsum先以严格候选唯一性给真实pairwise disjoint，再用共同AE覆盖取得可数和=μ(G)。marked_partition_tsum沿每候选上的真实nextMark值精确分解带mark事件。所有事件可测均有独立证明，未以形式求和替代概率覆盖。

## 公平law与停止σ独立来自真实flip对称

invariant_factor逐候选使用前模块实际fair flip half-factor，再ENNReal tsum乘法得到完整事件factorization。对G=E∈F_R，用已证明未揭示mark不改变R/E解除不变性参数，得μ(E∩{nextMark=b})=μ(E) fair{b}。

restricted_map_eq借Bool全部singleton确定有限measure，得到(μ.restrict E).map(nextMark)=μ(E)•fair。继而E=univ取得真正HasLaw，再对任意comap-Bool事件与F_R事件取得Indep。所选index可依赖past marks；没有套旧clock-only selection定理或把所需公平结论作为前提。

完整fair mark law需要明确AEfinite R以排除无future回退；不要求R≥0。非负R只在随后调用Exp残余survival时加入。此区分和量词在源码中保持。

## 联合等待—mark生存因子化直接证明

stopped_waiting_mark_factor对G=E∩{u<actual waiting}直接应用不变性：候选flip保持clocks和真正R，实际waiting逐样本不变，E也保持。因此先得到μ(E∩{u<W}∩{M=b})=μ(E∩{u<W}) fair{b}，再接已证同一R、同一site actual residual jointSurvival，取得u≥0时exp(-u) μ(E) fair{b}。

这个联合threshold identity没有从“waiting独立过去”和“mark独立过去”两个边缘独立结论偷推。它精确包含原F_R的任意事件E、同site等待和下一严格未来mark。当前Lean没有另行声明任意Borel子集上的pair HasLaw或Indep(pair,F_R)；若要该包装，可在后续用finite-measure tails唯一性扩展，不能把未写接口提前计为形式化。

## 实际boundedExit三个实例不假设原退出有限

最终三theorem实际代入ProtectedExitResidual.boundedExit=min(ENNReal exit,T)之后才toReal的合法原F停时版本。IsStoppingTime、pointwise ne_top及nonnegative全由此前模块证明，AEfinite来自pointwise事实；没有传入未经证明的unbounded physicalExit有限性或有限均值。

得到实际截断退出后的下一site mark公平HasLaw、与真实停止σ独立，以及同site等待/mark联合survival。exit=∞时截断取T而不是先toReal变0，这个既有边界保持。任意D/I/S参数可取实际clippedDomain/protectedSites/initialDomain；没有改变原率一clock、fair marks或物理时间尺度。

## 尚未完成

此组只闭合固定site下一ring的上述接口，不宣称多site residual向量联合独立、完整未来fresh field、全strongMarkov、物理生成元补偿、被禁出生累计控制、自含CMST/FSS或原τ(N)=Θ(N²)主定理。标准内核与独立AI复核不是人类专家认证。


## 最终统一证据绑定（2026-10-21）

实际统一时间2026-10-21T05:39:35.916899+08:00，2321分析辅助定理/171分析源，build_exit=axiom_audit_exit=0、kernel_trust_level=0。独立代理重新逐字节核全部171分析+8既有核心=179正式源，实际源集与JSON精确一致，本组三正式SHA同时匹配各专项和全局记录。完整2321分析及126核心公理输出与相应#print表逐名、逐顺序相同，含声明名内撇号；只标准三公理或无公理，无占位公理。

UnrevealedMarkInvariance9/12、StoppedMarkSlices12/13、StoppedFreshMark18/19，新增39theorem/44named，各专项及统一真实build/standardtrust0均通过，零新Lean warning。当前2446辅助定理及1模型，2447项全局公理输出。核心8源与既有验收相同，本次没有重新编译核心；既有batteries文档修改warning保留。审查代理未运行Lean或重新语义审阅所有旧证明。

因此前文“待统一”是形成时状态，当前新三模块全局验收已据真实证据闭合。nextmark完整fair law、停止σ独立、直接joint waiting/mark survival及实际boundedExit三个实例属于StoppedFreshMark，未倒归为前面不变性/切片模块单独成果。任意Borel pair-law包装、多site/fullfuture、物理补偿与被禁birth累计控制、自含CMST/FSS和完整主定理仍未完成。旧176源冻结报告保持原历史指纹未改；独立AI不等于人类专家认证。
