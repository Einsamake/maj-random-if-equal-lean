# 下一阶段：把真实 mixed-clock 过程接到 Dynkin 与矩方程

2026-10-25，只读源码接口研究。本文件没有新增 Lean 源、没有执行构建，不是已验收定理。当前有限角翻转、粒子编码/槽交换和有限生成元代数的正式验收，以 root 的实际记录为准；本文不把正在写的 `MixedExclusionGenerator` 当成已通过。

核心结论：**不需要重做等待时间、标记独立性或有符号补偿。需要新增的是一个有限状态更新机器的真正过去观测代表，然后把已有补偿用在它的真实事件增量上。** 旧面积 Dynkin 的 observable 虽然泛型，状态和更新仍固定为清理后冻结的 `Finset Site`，不能直接换成 mixed 更新。

## 1. 已有的真实过程与时间约定

`MixedSquareClockLaw.endpoint n t initial z` 的定义是

```text
MixedSquareModel.execute z.2 (ClockEventWord.word z.1 t).reverse initial
```

实际样本为 `ClockWordMarks.Sample n`，测度为 `ClockWordMarks.measure n`；这是每个有限格点的 rate-one 指数时钟与身份索引公平标记场的原乘积测度。`endpoint_measurable` 已证固定 t 的 ambient 可测性；`endpoint_monotone_shape`/`all_times_top_shape` 是逐样本、逐时刻的真实形状结论；`original_endpoint_le_mixed` 是同尺寸、同原始时钟/标记样本的逐样本比较。

这些接口**没有**证明 endpoint 对过去 history 适应，也没有给出其生成元积分公式。`ClockEventWord.word` 在 `Good` 不成立时返回空字，而 `Good ω t` 同时要求有限过去事件集和整个 `eventTime ω` 的单射性。后一个条件涉及未来。因而不能把 ambient 可测性、几乎处处正常、或“规则直观上只读过去”当成全样本 history 可测性的证明。

## 2. 可以原封不动引用的接口

| 接口 | 已经给出的事实 | 限制 |
|---|---|---|
| `EventTrace.execute_nil/cons/append` | 任意 `Label → State → State` 的有限顺序执行代数 | 不给概率、适应性或 telescope |
| `ClockEventWord.good_ae` | 任意有限顶点集 V 的一个共同满概率集上，所有实数 t 均有真正局部有限和无同时时钟事件 | 源 clock measure；乘积样本可用 fst 准保测运输 |
| `ClockEventWord.eventTime_positive_ae` | 一个共同集上所有身份的真正事件时刻为正 | 同上 |
| `ClockWordConsistency.marked_sample_good_ae L`、`ActualPreState.marked_all_events_positive_ae L` | 上述两个事实已直接运输到原 clock/mark 联合 law | `Sample L` 使用下述奇数尺寸接口 |
| `ClockWordConsistency.good_mono/reverse_word_eq_filter/reverse_word_prefix` | 在实际 Good 路径上，早时刻事件字是晚字的真实时间过滤/前缀 | 不依赖 droplet 状态 |
| `StrictClockPrefix.strictWord`、`word_left_locally_strict`、`word_at_event_eq_cons_strict` | 严格过去字、任意正时刻前的空隙、真事件时刻新增唯一 head | 泛型顶点 V；head 是 newest-first，执行须反转一次 |
| `ActualAreaTelescope.strictWord_eq_filter_horizon` | 当前真事件的严格过去字等于固定 horizon 字中更早事件的过滤 | 泛型 V；此条不含面积状态 |
| `ActualAreaTelescope.sum_map_eq_sum_toFinset` | 无重复有限字的 List.sum 与 toFinset 求和相等 | 泛型项/字，非面积专有 |
| `MarkedHistoryWords.fiber_measurable` | 完整有限过去身份字和已发生标记的 history 可测 fiber | 状态无关，但以 L 参数化 |
| `MarkedHistoryWords.chronological_ordered/identity_word_eq` | Good 路径上 fiber 中的身份字就是真实 chronological 字 | 状态无关 |
| `ObservedFrozenProcess.fiber_lists_eq` | 同一样本/时刻任意两个合法过去 fiber 的身份列表相同 | 虽在 Frozen namespace，签名没有 D/I/S 或状态，可以直接复用 |
| `ObservedProgressive.variable_fiber_measurable` | 在 `Iic t × Sample L` 的过去乘积 sigma 上，变时刻完整 fiber 可测 | 状态无关；可用于新代表的 progressive 性 |
| `MarkedPredictableCompensation.trim_eq_reference`、`integral_eq_reference` | 原真实事件点测度在标准 predictable sigma 上等于 `(dt × 原概率)/2` 的 trim；实积分相等 | 不是全 ambient product sigma 的测度相等 |
| `RealPredictableCompensation.bounded_predictable_integrable`、`bounded_predictable_absolutely_summable_ae`、`bounded_predictable_integral_eq_time` | 任意**全样本有界且标准 predictable**实 score 的实际身份事件和可积、AE 绝对可和，期望等于 `(1/2)∫dt E[score]` | score 的真正 predictability/界仍须新证明；时间是物理 Lebesgue 时间 |
| `RealPredictableCompensation.sample_integrable/time_mean_integrable` | 有界 ambient 强可测 score 的样本与时间平均可积 | 不替代可预测性 |

这里最后三条不依赖旧清理规则或面积 observable。当前公平标记的 `1/2` 已在原真实 law 中证明，不要把它改解释为“实际改色次数的均值”。

## 3. 哪些旧接口不能直接实例化

- `MarkedHistoryWords.indexedEvents` 把身份送到 `recenter L` 的 `DropletModifiedWord.Event`；`fiber_events_eq` 也是这个 recentered 事件列表。新的有限机器应直接处理身份/原 mark，不能假装这就是 mixed executor 的事件类型。
- `ObservedFrozenProcess.graph/state`、`ObservedPreState.graph/beforeState` 的返回值固定为 `Finset Site`，执行固定为 `DropletStoppedWord.stoppedWord`。前者的 `fiber_lists_eq` 可复用，后者的 `rational_future_eq` 也只涉及任意样本事件 E，能复用；其余图像/状态接口需泛型化。
- `ActualPreState.strictStateAt`、`beforeState_all_times_ae`、`stateAt_all_events_update_ae` 使用原 recentered 清理冻结 `stoppedStep`。它们证明的是旧过程，不能直接声称 mixed 的 beforeState 已验证。
- `WeightedAreaDynkin.value`/`bound` 是 `observable(U ∩ D)` 和 D.powerset 上的显式有限界；`increment` 读旧 `ObservedPreState` 后执行 `stoppedStep`。`stoppedWord_observable_telescope` 虽然对时间标签 α 泛型，状态/更新仍锁在此处。
- 其 `observable_change_dynkin_generator` 最终是 `MaskedAreaGenerator.frozenGenerator`，不是任意 finite transition 的 Dynkin。把 mixed config 编成 Finset 并取 I=∅，也不会把清理/零边界更新变成实际 mixed 更新，不能靠此省掉新桥接。

## 4. 最小新增层：保留旧随机 law，只泛型化有限状态重建

先固定一个 L，不改已有 waiting/mark law。令 `A` 为有初态 `a₀` 的有限离散状态，`step : Vertex L → Bool → A → A`。mixed 实例是 `A = SquareSpin.Config(parameter L)`、`step = MixedSquareModel.cellUpdate`。

建议新增两层，而不是复制整个概率依赖树：

1. **过去观测状态。** 定义一个纯有限执行器 `runMarked l ξ a₀`：按 chronological 身份列表 l 及其给定标记向量 ξ 顺序调用 `step e.1 (ξ i)`。可直接执行 `List.ofFn(fun i => (l[i],ξ i))`，不需要 recenter、不需要重新抽标记。
2. 定义 `observedGraph t a := ∃ l ξ, fiber L t l ξ z ∧ runMarked l ξ a₀ = a`；若有唯一值则取它，否则返回初态。由旧 `fiber_lists_eq` 与 fiber 里逐身份原标记相同证明图单值；由旧 `fiber_measurable` 的可数并证明所有样本上的 history 可测。有限 A 的离散 sigma 是实际配置 sigma，不能漏掉其识别。
3. 在 Good 路径上，用真实 canonical l=`word.reverse`、ξ=原身份 marks，证明这个观测状态等于真实 mixed endpoint。该等式须在**一个共同满概率集上对所有实数 t**成立，而非每个 t 分别换零测集。
4. **严格过去代表。** 复制 `ObservedPreState` 的有理数左侧常值图构造，但把状态换 A。借新状态的 history 可测性证明标准 predictable 可测，fallback 仍为 a₀。借泛型 `StrictClockPrefix.word_left_locally_strict` 证明它在共同集上对所有 `t≥0` 等于真实 `strictWord.reverse` 执行；0 时刻用所有事件为正与空字处理。
5. 利用 `word_at_event_eq_cons_strict` 和 `EventTrace.execute_append` 证明每个原身份 e 的真实跳跃是 `step e.1 (z.2 e)` 作用于该严格过去状态。这一步保留事件时刻，即可安全评价随机 ring，不用每个确定时刻各自的 AE 等式代替。

新 finite-state 图的 uniqueness 不需要清理、停止、Monotone 或概率上界。mixed 所需形状可另用 `MixedSquareCorners.execute_monotone`，并对图的 fallback/被选执行值传播；不应把未来所需的生成元或矩方程作为此层参数。

## 5. 从真实 score 到 mixed Dynkin：新增而未证明的步骤

对任意实际有限 observable `F : A → Real`，构造显式界 `B_F = ∑ a : A, ‖F a‖`。每次真实更新分数

```text
score v b (t,z) = F(step v b (beforeA t z)) - F(beforeA t z)
```

在全样本上满足 `‖score‖≤2B_F`，并由 beforeA 的 predictable 可测性得到强可预测性。随后可以**直接**调用旧 `RealPredictableCompensation` 三条 bounded predictable 定理，不再证明 fair mark/补偿法则。

还需真正证明以下连接，不能当成旧面积结论已有：

- 任意 finite-machine 的有限 chronological telescope。旧 `WeightedAreaDynkin` 的归纳证明可复用模式，但 theorem 本身锁状态；新 theorem 应用 `EventTrace.execute` 的泛型 step。strict-word/horizon 过滤直接引用旧通用引理。
- 固定 horizon 内真实身份求和等于 `∑v∑b pathSum(score v b)`。旧 `WeightedAreaDynkin.bool_sum_term`、有限支持 reindex 证明仅需把 increment 参数化；当前这几个 theorem 的签名仍锁旧 increment，所以是少量泛型化，不能直接引用为已成 mixed 结论。
- 原 endpoint 的 F 值可积（有限界直接给出），绝对事件和可积、时间均值可积均先确立，再交换积分与有限/可数和。
- 得到真公式 `E[F(X_T)] = F(a₀) + ∫_(0,T] E[G_mixed F(beforeA_u)] du`。site rate 为1、两个指定 mark 各1/2；不能再额外加或删一个1/2。
- 若要写成 `G_mixed F(X_u)`，还须证明严格过去与当前端点在 `dt × 原概率` 上 AE 相同。每条 Good 路径只有可数个事件时刻，故可走“新观测状态 joint/progressive 可测 + 可数 jump times 零 Lebesgue 测度 + Fubini”的路线。`ObservedProgressive.variable_fiber_measurable` 可直接供新状态的 joint measurability。这里只说明最短候选证法，本次未找出可直接调用的完整 mixed before=endpoint a.e. theorem。

fixed-t `endpoint_measurable` 不能代替上一条 joint measurability；共同路径集合上的∀t相等也不能把事件时刻的 before/current 值错误地判为相同。

## 6. 真生成元等价完成后，才进入矩积分方程/ODE

`FiniteExclusionGenerator` 是纯有限代数；`MixedExclusionGenerator.actual_generator_eq_exclusion` 若实际验收，将把同一 mixed 状态的 fair-cell 生成元识别为相邻槽交换 rate1/2。它本身不提供过程的 Kolmogorov/Dynkin 方程。

在第5节真实积分式完成后，取 `F_i(f)=density(slotState f)i`、`F_ij(f)=density(slotState f)i*density(slotState f)j`，交换已证明可积的有限和，才能得到真正

```text
m_i(T)=m_i(0)+∫₀ᵀ(Q m(u))_i du,
g_ij(T)=g_ij(0)+∫₀ᵀ(Q2 g(u))_ij du.
```

有限系数和有界 observable 先给积分方程与绝对连续/连续性；再由连续 integrand 与微积分基本定理升级到 t>0 的矩 ODE。0 端点要用右导数或单独约定，不从形式生成元直接宣布可微。

之后仍须证明有限 Q2 的正性/比较原理，使用已证 product defect 的非负源项推出**不同槽 i≠j**的非正协方差；对角协方差是 Bernoulli 方差，不能混入“全矩阵≤0”。`rightCount_eq_rightSlotCard` 只是把标签数接成真实槽占据数，使后续方差展开有合法对象；它还不是方差界或粒子负相关。

## 7. 奇数尺寸与原 N：可保守选辅助边长8N+1，但连接未自动成立

旧补偿/联合 history 接口固定在 `DropletClockLaw.Sample L = ClockWordMarks.Sample(parameter L)`，其中 `parameter L=2L−1`，L≥1时实际边长为2L+1。因此最短实现先做 **n=parameter L 的 mixed 实例**，可以原封复用全部已证补偿；无需立即把旧随机基础逐模块泛型成所有 n/V。

若后续几何允许辅助方框边长 M=8N+1，取 L=4N，则 n=8N−1、M=n+2。对 N≥1，M≤9N，所以真正的 O(M²) 估计可转成 O(N²)，至多把该平方常数乘81；时间仍是 rate-one/site 的物理时间，不能用M²站点数再重标。

这是尺寸选择方案，**不是已证原N上界**。仍须按最后实际几何比较证明：原恰N归一化初态如何放入辅助框、目标区域/对角测试为什么足以原恢复、原 clock law 或同步 law 的具体运输、以及最后 clock↔同步时间比较。目前 `MixedSquareClockLaw.original_endpoint_le_mixed` 只有同尺寸比较，不能直接当跨尺寸 clock restriction。若最终改为“在同步层先嵌入更大框”的路线，现有 `SquareGridLaw.supported_tail_le_top` 可供支持比较，但也必须核对它所控制的完整方框恢复事件是否正是 mixed 论证给出的事件，不能把局部对角清空换成大框全灭绝。

结论范围：本路线尽量复用真实原 law；新数学缺口集中在 finite-state past/predictable 桥、实际 telescope/Dynkin、before/current 的时间-AE连接与矩方程。完整自含上界、负相关、谱/集中及原模型最终比较均未由本次接口核查证明。

