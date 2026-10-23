> 实现状态更新（2026-10-23）：下列原先只读设计现已实现为 `formal/drafts/PhysicalAreaGenerator.lean`，10 个定理。全稿标准 Lean --trust=0 与 10/10 命名声明公理审计均 exit 0；仅 Classical.choice、Quot.sound、propext，无新增 Lean 警告。正式统一验收由主代理单独完成；不得仅凭草稿证据宣称完整主定理完成。原文“尚未验证”表述描述设计撰写时状态。

# 下一小阶段：把真实面积累计式接上固定区域生成元

只读设计；未新增 Lean、未运行构建，以下候选接口均不表示已获 Lean 验收。按当前实际源码核查，日期 2026-10-23。

## 最短数学路线

令 `A(U)=((D \ U).card : Real)`，`R=recenter L`，`V=Vertex L`。所需桥是

`(1/2) * Σ(v:V) Σ(b:Bool) [f(stoppedStep D I U (R v,b))-f(U)]`

`= frozenGenerator D I U f`。

**通用版本必须要求 `D ⊆ centeredSites L`。** `recenter_injective` 对所有 L 成立，`centeredSites L` 定义就是 `Finset.univ.image (recenter L)`，不需要新增双射或概率前提。任意 U、I、f 都可用；这一纯代数等式不要求 U⊆D、稳定性或 GeometricGood。

最短证明：

1. 新增 `stoppedStep_of_not_mem`：若 x∉D，`stoppedStep D I U (x,b)=U`。展开 stoppedStep，分 `I⊆U`；活跃支用 `DropletModifiedWord.modifiedStep_of_not_mem`。特别不要求 U 稳定；域外事件不会触发 cleanup。
2. 记 `g x=Σb [f(stoppedStep D I U (x,b))-f U]`。域外 `g x=0`。
3. 由 `Finset.sum_image (recenter_injective L).injOn` 把 `Σv g(R v)` 改为 `Σx∈centeredSites L g x`。由 `Finset.sum_subset hD` 及域外零项改为 `Σx∈D g x`。
4. 分配系数 1/2，对每格用 `Fintype.sum_bool` 展开两标记，`ring` 对齐 frozenGenerator。Bool 求和实际顺序 true/false 无影响。不能再额外除以格子数或引入总响铃速率。

候选最少接口（均为未验证设计名）：

- `stoppedStep_of_not_mem (D I U) (x) (b) (hx:x∉D)`。
- `finite_vertex_generator_eq (L) (D I U) (f) (hD:D⊆centeredSites L)`：上述任意可观测量恒等式。
- `area_rate_eq_generator (L D I S) (hD) (p:NNReal×Sample L)`：取 U=beforeState(p)，f=A，得到 `(1/2)*ΣvΣb increment(...,p)=frozenGenerator ... A`；全样本逐点成立。

若无覆盖，一般 D 的结论不成立：D 可为有限时钟正方形外的单格，U=D、I=∅，所有已表示格子的事件均不改变 U，而对域内唯一格的 frozenGenerator(A) 为 1。现有任意 D 的 finite-vertex Dynkin 式没有因此出错；它只累计真实有限顶点的事件。不能直接将其说成任意 D 的完整 D-site 生成元公式。

## 真正 clipped 参数实例，不留覆盖为最终假设

采用已有原辅助过程参数：

- `D = ClippedDiamondGeometry.clippedDomain L`；即 |x|≤L、|y|≤L、|x|+|y|≤L+1。
- `I = ClippedProtectedGeometry.protectedSites L`；它是内菱形与真正外四邻边界的并集，不得替换为内菱形本身。
- 初态 `S=D`；`parameter L=2*L-1`，每个真实有限顶点独立速率 1、每色标记速率 1/2。
- 代数覆盖只需 `1≤L`，直接应用 `ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL`。原 CMST/退出几何入口保持 `40≤L`，用 `by omega : 1≤L`，不把 hD 留在最终实际定理。

候选实际 wrapper `actual_clipped_area_rate_eq_generator (L) (hL:40≤L) (p)` 应无任意 D/I/S、覆盖、过程概率或漂移参数。

进一步由 `ObservedPreState.state_supported L D I (Finset.Subset.refl _) p.1 p.2`，实际 beforeState 在全样本上都包含于 D；再应用 `ProtectedAreaPotential.missing_area_generator`，得到精确

`generator(A) = if I ⊆ beforeState then rawAreaRate D beforeState + cleanupRate D beforeState else 0`。

这一步不需要 GeometricGood，却也不产生任何常数漂移界。禁止恢复已否定的 masked 恒漂移 2，禁止把 forbidden-birth 修正用 cleanup 预算支付。

## 接上已证明的真实 Dynkin

已有 `ActualAreaDynkin.area_change_dynkin_single_integral` 的右端为
`(1/2) * ∫_Ioc(0,T) Σv Σb E[increment(v,b,t)] dt`。

- 对每个确定 u，先用 `RealPredictableCompensation.sample_integrable`，输入 `increment_stronglyMeasurable`（降到 ambient sigma）与 `increment_norm_le`，获得各原 μ 内积分可积。
- 两次 `integral_finsetSum` 将有限求和移入原 μ 积分；用上述逐点 rate 恒等式，保持 1/2 恰好一次。
- 用两层 `integrable_finsetSum` 与已有 `ActualAreaDynkin.time_mean_increment_integrable` 建立时间上的有限和可积；`const_mul` 后由逐点积分恒等式搬运到 `E[generator(A)]`。真实时间仍是 Real Lebesgue 在 Ioc 0 T 上的积分，NNReal 仅通过 u.toNNReal 传给 beforeState。
- 由现有公式可得 `E[A(stateAt(T))-A(S)] = ∫_0^T E[generator(A)(beforeState(t))] dt`，再用 `expected_area_dynkin` 或已知面积可积重写期望面积。实际 S=D 时初始缺失面积为 0。

建议下一独立小阶段验收范围：纯 reindex/域外零项；一般覆盖版生成元 Dynkin；真实 clipped、真实保护集/初态无覆盖参数的实例；beforeState 支持下 raw+cleanup 的实际实例；所需生成元时间均值可积。约 8–12 个辅助定理，主要为有限求和、可积性与已有代数拼接。

不把 progressive 当 predictable，不补新的停时定理，不改已闭合事件补偿/望远镜。这里的生成元属于实际随机标记驱动的 masked-cleaned-first-loss-frozen 连续时钟辅助过程；不是声称同步原过程本身拥有这个连续时间生成元。同步/时钟比较沿用已证明连接。

## 窗口判断

在下一个可用窗口完成上述独立小阶段是合理目标：关键实际覆盖、单射、域外恒等、面积势生成元、每项真实可积性均已有，不含新的 CMST/FSS 数学核心。主要风险是有限求和/标量的 Lean 规约与完整统一验收耗时，不是未证概率法则。

当前 root 报告 primary 已用 52%，且本轮新 Dynkin 尚须完整统一审计、独立核对、文档/材料包及私有快照。建议本轮先把这些实际验收和交接完成，不为新增代数模块挤占保全预算；在下个真正有可用额度的窗口将此作为完整小阶段。无承诺性耗时估算：通常 1 个有效工作窗口足以检验，若发现接口偏差如实记为未完成。主定理和自含 CMST/FSS 收缩尾仍未验收。

## 核查源链接

- [recenter、单射与真实有限像](../analysis/MathResearchAnalysis/ClippedSquareCoordinates.lean)，单射在 43，centeredSites 定义在 79。
- [真实 clipped 顶点像覆盖](../analysis/MathResearchAnalysis/ClippedSquareCoordinates.lean)，[clippedDomain⊆centeredSites](../analysis/MathResearchAnalysis/ClippedSquareCoordinates.lean)。
- [域外 modifiedStep 恒等](../analysis/MathResearchAnalysis/DropletModifiedWord.lean)，[stoppedStep 定义](../analysis/MathResearchAnalysis/DropletStoppedWord.lean)。
- [frozenGenerator 定义](../analysis/MathResearchAnalysis/MaskedAreaGenerator.lean)，[有支持前提的真实缺失面积生成元](../analysis/MathResearchAnalysis/ProtectedAreaPotential.lean)。
- [beforeState 全样本支持](../analysis/MathResearchAnalysis/ObservedPreState.lean)，[实际单事件 increment](../analysis/MathResearchAnalysis/PredictableAreaContribution.lean)。
- [已有单时间积分 Dynkin](../analysis/MathResearchAnalysis/ActualAreaDynkin.lean)，[每项时间均值可积](../analysis/MathResearchAnalysis/ActualAreaDynkin.lean)。
- [真实样本内积分可积](../analysis/MathResearchAnalysis/RealPredictableCompensation.lean)，[真实时间均值积分可积](../analysis/MathResearchAnalysis/RealPredictableCompensation.lean)。
