# 真实下一site-ring候选的公平切片：独立AI复核

2026-10-21，代理`/root/history_audit_1021`。只读正式冻结StoppedMarkSlices、已审未揭示mark不变性及实际审计日志；未改Lean、未构建、未派代理，不作人类专家或新颖性认证。

## 专项证据与准确范围

正式12条theorem/13named（1def），SHA256 `613902a397525f9fcc884d78fe3bb0f1a096965e0e5eb48614f7e10f048ac276`，与[专项JSON](stopped-mark-slices-stage-declarations-validation.json)匹配。实际[build](stopped-mark-slices-stage-declarations-build.log)与[13项公理输出](stopped-mark-slices-stage-declarations-axioms.log)均exit0、standard Lean --trust=0，仅标准三公理，零新Lean warning；声明与输出顺序逐项匹配。专项时间2026-10-21T05:34:35.721321+08:00。

**精确语义、专项及最终统一证据通过（最终绑定见文末）。** 这是逐候选切片定理；完整nextMark定义、全测覆盖及完整law仍属于后续StoppedFreshMark，不以此阶段提前报成功。

## 真正第一个严格未来site identity

candidate要求R<arrival(v,k)，且每个j<k均arrival(v,j)≤R。实际chronologicalArrival按index单调，所以它是该固定site在R之后的首个严格未来identity，不把arrival=R已经揭示的mark作为fresh。candidate_unique直接用两候选的前序条件排除不同index，保持(site,index)身份，没有合并同site多次ring。

candidate内R已严格小于有限Real到时，因此该样本R有限，足以调用前模块未揭示mark不变性。本阶段不需要R≥0、R全局AEfinite或原物理退出有限的输入。R=∞时没有任何候选，局部切片结论仍成立；只有后续完整候选覆盖会需要AEfinite/cofinal。

## flip保持R、候选、停止过去和实际waiting

candidate_flip_stoppingTime以实际停止σ可测R及严格未揭示条件取得flip(v,k)后R不变。clock坐标完全保持，所以该候选的所有到时条件也保持；再用真实flip involution得到候选双向等价，而不只是从候选向前保持。

candidate_stopped_event_flip_iff准确用于E∈F_R，R可依赖过去marks。candidate_waiting_flip展开同一actual after及R的定义，保持clock和R后逐样本实际残余waiting相同；它没有假设mark与waiting独立作为输入。

## 从保measure对称到half质量

flip_slice_measure用已证真实fair clock×marks product保measure及A的不变性，证明mark=b与mark=!b切片互换。fair_slice_factor再用Bool的两切片disjoint且并为A，得到每片是μ(A)/2。ENNReal逆2取消只使用2非零/非∞，兼容μ(A)=0或∞，不隐藏所需恢复时间可积性。

candidate_slice_factor把A取为candidate(k)∩G；其G不变性是一般结构条件，后两个具体定理分别对G=E和G=E∩{u<waiting}用已证停止事件/实际waiting不变性解除该参数。因此不是把所欲公平结论当作前提。

## 联合等待事件已真正纳入切片

stopped_waiting_slice_factor在同一不变候选中包含停止历史E、实际waiting阈值和新mark，直接得到half μ(candidate∩E∩{u<waiting})。它不从两个边缘独立结论偷推joint独立；u在本切片阶段可任意Real。后续接Exp survival时才需u≥0及非负、AEfinite的实际R条件。

尚无完整随机nextMark law、任意Borel pair-law theorem、多site residual向量或完整future strongMarkov，物理补偿、CMST/FSS及原主定理仍需继续。


## 最终统一证据绑定（2026-10-21）

实际统一时间2026-10-21T05:39:35.916899+08:00，2321分析辅助定理/171分析源，build_exit=axiom_audit_exit=0、kernel_trust_level=0。独立代理重新逐字节核全部171分析+8既有核心=179正式源，实际源集与JSON精确一致，本组三正式SHA同时匹配各专项和全局记录。完整2321分析及126核心公理输出与相应#print表逐名、逐顺序相同，含声明名内撇号；只标准三公理或无公理，无占位公理。

UnrevealedMarkInvariance9/12、StoppedMarkSlices12/13、StoppedFreshMark18/19，新增39theorem/44named，各专项及统一真实build/standardtrust0均通过，零新Lean warning。当前2446辅助定理及1模型，2447项全局公理输出。核心8源与既有验收相同，本次没有重新编译核心；既有batteries文档修改warning保留。审查代理未运行Lean或重新语义审阅所有旧证明。

因此前文“待统一”是形成时状态，当前新三模块全局验收已据真实证据闭合。nextmark完整fair law、停止σ独立、直接joint waiting/mark survival及实际boundedExit三个实例属于StoppedFreshMark，未倒归为前面不变性/切片模块单独成果。任意Borel pair-law包装、多site/fullfuture、物理补偿与被禁birth累计控制、自含CMST/FSS和完整主定理仍未完成。旧176源冻结报告保持原历史指纹未改；独立AI不等于人类专家认证。
