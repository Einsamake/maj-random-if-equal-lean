# 实际到时与揭示标记的最小历史：独立只读审阅

代理 `/root/boundary_method_record`，2026-10-19（北京时间）。只读新MarkedClockFiltration及其已有arrival-history接口；不修改Lean、不构建、不重审旧2144条，不冒充人类专家认证。

当前冻结正式源码14条theorem、18个def/abbrev/theorem命名项，含新增coverage/finite-arrival判据。2026-10-20独立只读补核最终专项及统一JSON/log：18个新增命名项实际标准trust0输出完整，build/audit均0；统一2158分析定理/158分析源实际build/audit0，当前模块SHA同时匹配专项和统一记录。加既有8核心源共166正式源；没有重审全部旧定理，也不因此认证人类专家审查。

## 实际信息与最小性

`observations L t` 恰包含每个真实identity e的arrival(e)≤u，以及arrival(e)≤u且其mark(e)=b，u≤t。`history` 以这些事件generateFrom，再从u≤s≤t证明单调；其所有generator在原clock×mark总σ代数中确实可测。代码没有把globalGood、全未来mark field或全未来arrival精确值加作generator。

`arrival_measurable`与`mark_measurable`仅为原ambient product space的可测helper，用来证明history≤ambient；后者并未宣称任意未来mark对当前history可测。actual eventTime是既有total chronological代表，和真实指数partial sums的AE识别由旧模型供应。

`history_le_of_observations` 证明任何filtration只要观察到这两类真实事件，最小joint history就包含于它。`arrival_history_le` 通过实际每个arrival_isStoppingTime接已有纯arrival history的最小性，方向是纯arrival≤joint。当前每个实际ring的stopping性质由其≤t阈值本身就是generator取得，不是额外假设。

## 揭示函数明确保留none与some

`revealedMark` 在arrival≤u时为some真实mark，否则none。none fiber是未到时事件补集；some b fiber恰是已到时且mark=b。显式 `markSpace=⊤` 是三值Option Bool的离散σ代数，局部history实例只用于lemma elaboration，没有新全局孤立instance或悄悄改ambient measure。

逐fiber与逐identity证明给出history t下u≤t的揭示field可测；它记录哪些ring已发生及其mark，不把未来ring的mark提前作为可见值。没有额外声称未揭示mark的条件独立性或强马氏。

## 真正的“历史不能区分不可见变化”证书

`measurable_event_past_invariant` 假设两个样本对每个identity、每个u≤t的arrival阈值同值，且对已到时identity的实际marks相同。ha在u=t保证两样本已到集合相同，所以hm只写一侧已到也足够。

代码逐generator核同值，marked分支正反方向的mark等式正确；随后调用mathlib `forall_generateFrom_mem_iff_mem_iff`，提升为**任何当前history可测事件**都不能区分这两个样本。这是点态σ代数结论，不是仅凭文件注释说“没有未来信息”。

作用域仍限原generateFrom history。将来加completion时，null样本上的点态不可区分性不自动保留；不能未经限定将本lemma搬到完成历史。

## 当前边界

本模块建立实际joint filtration、ring停时、Option Bool揭示field可测、最小性与观察等价不变性。尚未证明total clock word适应性或physicalExit的IsStoppingTime，未解决global fallback与完成历史的适配，更无生成元、补偿、强马氏或CMST/FSS核心概率结论。源码不包含这些目标作为输入。

最终18名实际源码与标准trust0输出、冻结SHA已于2026-10-20只读绑定；只见propext、Classical.choice、Quot.sound。专项和统一exit0，无新Leanwarning，既有batteries本地docs修改warning保留。代理没有启动任何Lean或编辑源码。

## 当前时刻coverage与local-finiteness判据

新增 `coverage_measurable` 将“有限字l恰枚举所有已到identity”写成对countable Event identity的可数交；每个iff仅比较常量membership和当前history的arrival≤t事件。`finite_arrivals_measurable` 再以countable List Event作可数并：有限eventSet取其actual toFinset/toList作见证，反向由完整coverage把eventSet嵌入有限l。双向均有真实证明，没有将覆盖单向或随便给定有限字当成全部事件。

由此当前时刻localfinite fallback判据确对最小joint history可测，但旧totalword的另一个判据是global eventTime injective。它涉及未来碰时，尚未由本模块证明当前可见，也不能从新localfinite可测性自动推旧totalword点态适应。若两个样本过去完全一致而只改变未来碰时，原globalGood fallback可能使旧word在一个样本保留过去字、另一个样本变空；后续需准确处理局部代表或完成历史，而不是把新lemma冒称全部fallback已经适应。


## 最终证据补核（2026-10-20）

模块SHA256：`bb62f020596e7712eb99754909f143878696b2f8496ea73d6d7a594104f9e99c`。[专项验证](marked-clock-filtration-stage-declarations-validation.json)时间2026-10-19T21:21:32.280896+08:00，18个具名输出与JSON声明表逐项一致；[统一验证](analysis-validation.json)时间2026-10-19T21:22:08.433050+08:00，2158分析定理及158分析源，build_exit=axiom_audit_exit=0，kernel_trust_level=0。当前模块字节同时匹配两份指纹。此补核仅完成原报告缺失的最终证据绑定，没有重审所有旧证明，也不把后续MarkedHistoryWords草稿算作本阶段结果。
