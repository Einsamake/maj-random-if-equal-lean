# 未揭示identity mark不变性：独立AI复核

2026-10-21，代理`/root/history_audit_1021`。只读正式冻结的UnrevealedMarkInvariance、原joint历史生成元与真实fair product接口及实际审计日志；未编辑Lean、未构建、未派代理。不冒充人类专家或数学新颖性认证。

## 专项证据与范围

正式源码9条theorem/12named（3defs），SHA256 `0aa824e23cdea413b5e6e4973b7a80dbea33fce53ff261b4c88a99c5f58df225` 与[专项JSON](unrevealed-mark-stage-declarations-validation.json)逐字节一致。[真实build](unrevealed-mark-stage-declarations-build.log)和[12项完整公理输出](unrevealed-mark-stage-declarations-axioms.log)均exit0、standard Lean --trust=0，仅标准三公理，零新Lean warning，声明与输出顺序逐名相同。专项时间2026-10-21T05:27:42.144195+08:00。

**精确语义、专项及最终统一证据通过（最终绑定见文末）。** 此阶段只证明未揭示mark不变性和真正flip保measure；下一mark公平/half-factorization尚属后续路线，不以本模块冒称已完成。

## strict未揭示条件与真实过去

replaceMark只改指定(site,arrival-index)身份e的Bool，保留整个clock场及其余mark。history_invariant在r<arrival(e)条件下逐已揭示mark检查：任何已到r的d都不可能是e，因此joint历史的所有arrival和已揭示mark观察完全相同，再由已证generated σ代数不变性覆盖全部F_r事件。

strict不等号是必要的。若arrival(e)=r，mark已在F_r揭示，过去事件或停时可以依赖它；源码没有把strict条件放宽，也没有把新mark标成“整个未来独立”。无globalGood、局部有限或新的概率law假设。

## 真正停时R和停止σ事件同样保持

stoppingTime_invariant要求样本当前R等于有限Real r且r<arrival(e)。先对{R≤r}的过去事件应用不变性，得到替换后Rw≤r。若替换后更早Rw=s<r，再对{R≤s}在s<arrival(e)处应用同一过去不变性，反推原R≤s，与原R=r矛盾。因此双向R值确实相同，不是仅证明它仍有某上界。

stopped_history_invariant使用F_R定义中的E∩{R≤r}∈F_r，并在两样本R相同后消去阈值，精确得到E成员资格不变。允许R与E依赖已经揭示的过去marks；没有假设R只读clocks或使用更大的全future历史。

当R=∞时本lemma不作有限r识别。后续候选R<某有限arrival会自动强制该样本R有限，所以局部候选不变性不需假定原physicalExit必有限；完整候选AE覆盖仍须另证。

## 单坐标公平翻转保持真实law

flipField只在e上用Bool.not，逐坐标可测、两次翻转恒等。flipField_map使用实际infinitePi逐坐标map和已证真实fair_map_not，非e坐标为identity，得到原markMeasure保持；没有引入一个抽象可替换law作为输入。

flipSample保整个clock坐标、只改上述mark场，实际clockMeasure×markMeasure的product map公式给原ClockWordMarks.measure保持。可测、involutive与map等式都在正式代码中证明。它是下一候选切片对称的真实measure工具，不等于已经证明随机选择mark公平。

## 下一路线与必须保留的边界

下一步可对第一个R后site identity k的候选A使用flip(v,k)：R、F_R事件E和候选都不变，而mark=b/!b切片互换，望取得half μ(A)，再通过唯一性与真实AE覆盖sum_k。nextIndex会依赖past marks，不能套旧clock-only selection theorem。

若要joint(wait,newmark)，需把waiting阈值事件也纳入不变候选并证明联合factorization，不能从waiting和nextmark各自独立过去的两个marginal结论推出pair law。多site残余向量、fresh future fields、完整strongMarkov、物理补偿及自含CMST/FSS主定理仍未完成。


## 最终统一证据绑定（2026-10-21）

实际统一时间2026-10-21T05:39:35.916899+08:00，2321分析辅助定理/171分析源，build_exit=axiom_audit_exit=0、kernel_trust_level=0。独立代理重新逐字节核全部171分析+8既有核心=179正式源，实际源集与JSON精确一致，本组三正式SHA同时匹配各专项和全局记录。完整2321分析及126核心公理输出与相应#print表逐名、逐顺序相同，含声明名内撇号；只标准三公理或无公理，无占位公理。

UnrevealedMarkInvariance9/12、StoppedMarkSlices12/13、StoppedFreshMark18/19，新增39theorem/44named，各专项及统一真实build/standardtrust0均通过，零新Lean warning。当前2446辅助定理及1模型，2447项全局公理输出。核心8源与既有验收相同，本次没有重新编译核心；既有batteries文档修改warning保留。审查代理未运行Lean或重新语义审阅所有旧证明。

因此前文“待统一”是形成时状态，当前新三模块全局验收已据真实证据闭合。nextmark完整fair law、停止σ独立、直接joint waiting/mark survival及实际boundedExit三个实例属于StoppedFreshMark，未倒归为前面不变性/切片模块单独成果。任意Borel pair-law包装、多site/fullfuture、物理补偿与被禁birth累计控制、自含CMST/FSS和完整主定理仍未完成。旧176源冻结报告保持原历史指纹未改；独立AI不等于人类专家认证。
