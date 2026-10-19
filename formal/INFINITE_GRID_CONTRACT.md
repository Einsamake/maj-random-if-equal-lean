# 有限方形与无限整数格点：已实施合同及保留边界

原合同制定于2026-10-14，以下正文保留当时的精确验收要求。2026-10-15已形成对应实际源码：原点完整extension、任意Supported版本、整场pushforward、含∞首达law、一般平移及奇phase、状态／marks补与同步全一目标首达；本轮统一验收已通过，结果见 [新阶段记录](PROGRESS_2026-10-15_GRID.md)。真实确定时刻重启及past／future独立也已接入。原尺寸／直径、边长0／1及最坏期望量词仍为后续范围；CMST／FSS核心尾与完整主定理没有因此完成。下文的“待创建”“下一阶段”是原合同语境，不是当前待办；当前接续以 [NEXT_PHASE](../README.md) 为准。

## 已核对的起点

- [核心 Grid](MathResearch/Grid.lean) 的 `Site=Int×Int`、`Inside L z` 为 `[0,L)²`，`Supported` 要求域外全 false；真实规则只读 north/east/south/west，不读中心。`neighbour_ones_le_one`、`update_supported`、`synchronous_supported`、`alternating_supported` 已有确定性证明。
- [核心 Majority](MathResearch/Majority.lean) 的阈值为四方向 true 数严格大于／小于 2，恰为 2 使用 tie。它不带公平分布假设。
- [SquareSpin](analysis/MathResearchAnalysis/SquareSpin.lean) 在 `Vertex n=Fin(n+2)×Fin(n+2)` 上有四个方向零边界输入及 `ones_eq_four_inputs`；越界方向确为 false，不能变成内部邻居可变度多数。
- [SquareDynamics](analysis/MathResearchAnalysis/SquareDynamics.lean) 与核心的同步和交替递推都在输出槽 `t+1` 使用 `marks(t+1)`；交替 phase 是初始颜色，第一正槽更新 `!phase`。[BipartiteDynamics](analysis/MathResearchAnalysis/BipartiteDynamics.lean) 已迁移并在 rc4 重编译，可对无限 Site 复用。
- [SquareRandomDynamics](analysis/MathResearchAnalysis/SquareRandomDynamics.lean) 的样本为 `(Vertex n×Nat)→Bool`，`marks η j v=η(v,j)`；真实测度是 `FairMarks.markMeasure (Vertex n×Nat)`。时间零硬币存在于积空间但不参与更新。

**工具链边界：**核心使用 Lean 4.35.0，分析使用 4.35.0-rc4。不可将核心 `.olean` 加到分析导入路径。后续在分析 namespace 下显式迁移必要 Grid／四输入规则及支持几何并注明来源，直接复用已迁移 BipartiteDynamics；不要重复迁移 Dynamics 或制造同名 `MathResearch.Grid`。

## 第一小阶段：确定性逐时刻连接

范围只取原点方形、边长 `L=n+2`、外零背景。可将新分析模块命名为 `InfiniteGridModel` 与 `SquareGridEmbedding`；这些是待创建名字，不是已经存在的源码。

先建立真实无限模型：`Site := ℤ×ℤ`，固定任意 `Marks := Nat→Site→Bool`，四方向和核心一致，`system marks : BipartiteDynamics.BipartiteSystem Site`。四输入更新定义与核心 Majority 逐项相同，局部性／零保持必须实际证明。

规定 `embed n v=((v.1.val:ℤ),(v.2.val:ℤ))`；`restrict n f v=f(embed n v)`；`extend n g` 在 `[0,n+2)²` 内用唯一有限顶点读 g，外部为 false；`restrictMarks n marks j v=marks j(embed n v)`。禁止在负整数坐标处仅调用 `Int.toNat` 而省略域内判定。

第一阶段必须交付以下真实声明，名字可按模块统一，命题不可削弱成假设：

1. `embed_injective`，`inside_iff_exists_vertex`：`Inside(n+2) z ↔ ∃v,embed n v=z`；`restrict_extend`；`extend_restrict`，后者唯一额外条件为真实 `Supported(n+2) f`。
2. `extend_north/east/south/west`：例如 `extend n g (north(embed n v)) = SquareSpin.northInput g v`，其余三式相应。由此证明 `update_embed`：无限四方向更新在 `embed v` 等于 `SquareSpin.rule g v (marks j(embed v))`。有限计数中 east/west/north/south 与核心 north/east/south/west 的排列需明确消解。
3. `colour_embed`：原点嵌入保持真实整数／自然数棋盘颜色。实际证明外点最多一个内部邻格，进而给出无限同步、交替轨迹支持保持；不能把 support invariant 当结构公理。
4. `synchronous_extend`：对任意全格 marks、有限初态 g 和任意 `t:Nat`，

   `InfiniteGrid.synchronous marks (extend n g) t = extend n (SquareDynamics.synchronous (restrictMarks n marks) g t)`。

5. `alternating_extend`：同式换成交替轨迹，原点嵌入使用相同 phase。也可从真实 splitting、`colour_embed` 及同步等式推出，避免重复一套递推。

**首阶段验收终点是两条完整配置函数等式**，不止局部规则或单时刻限制值。外点值由真实支持保持证明；内点由四方向恒等式证明。对任意 Supported 无限初态 f，通过 `extend_restrict` 得到一般版本，而非预设所有初态已写成 extend。构建、逐公开定理公理审计、禁用构造扫描与哈希按现有机制执行。

## 第二小阶段：实际随机 law 与无穷首达

使用 [FairMarks](analysis/MathResearchAnalysis/FairMarks.lean) 的真实积空间，定义全格 `Sample := ((ℤ×ℤ)×Nat)→Bool`、`measure := FairMarks.markMeasure ((ℤ×ℤ)×Nat)`，`marks η j z=η(z,j)`。限制映射是整个时空场

`restrictSample n η (v,j)=η(embed n v,j)`。

需要从 `embed_injective` 实际推出索引注入 `(v,j)↦(embed v,j)`，证明 restriction 可测，并用现有 `Measure.map_infinitePi_infinitePi_of_inj` 得到

`Measure.map (restrictSample n) InfiniteGrid.measure = SquareRandomDynamics.measure n`。

该结论包含所有自然数时刻，不能用“每个硬币公平”或只覆盖有限前缀的结论替代整场联合 law；不得将 restriction 的 HasLaw 或独立性作为最终前提。当前 FairMarks.fixedSelection_hasLaw 提供的是有限向量接口；这里直接使用其证明所依赖的无限积注入映射定理。

将第一阶段逐样本轨迹等式代入，证明无限过程切片可测，并得到真实有限轨迹／尾事件概率相等。再用 [ExtendedRecoveryTime](analysis/MathResearchAnalysis/ExtendedRecoveryTime.lean) 和 [SquareRecoveryTime](analysis/MathResearchAnalysis/SquareRecoveryTime.lean) 定义无限 `ℕ∞` 首达。证明 `extend n g=全零 ↔ g=全零`，从所有时刻零事件一致推出

`infiniteRecovery (extend n g) η = SquareRecoveryTime.synchronous n g (restrictSample n η)`，交替同理。

等式必须包括两侧都为 ∞ 的样本，不接受有限首达见证作为前提；可用 `time_le_nat_iff` 的阈值刻画和 ENat 外延，或直接比较两个首次命中集合。全格空间是无限配置空间，不能对它误用“有限状态所以任意函数可测”；可用配置坐标可测性，或支持限制后的 extension 表达式。由整场 pushforward law 再得首达 law／尾概率相等，暂不证明期望有限或二次尺度。

## 后续边界，暂不并入首阶段

- **平移：**一般方形 `a+[0,L)²` 需同步平移初态和所有时空 marks，再证明积测度在坐标双射下不变。若 `a.1+a.2` 为奇数，棋盘颜色翻转，交替 phase 也须翻转；同步平移不涉及 phase。
- **全一背景：**需同时对状态和 tie marks 取补，证明实际四输入规则补对称及公平积测度的补映射不变，不能声称同一硬币样本自动给互补轨迹。
- **尺寸／直径：**当前有限参数 n 的边长是 `n+2`，原问题的扰动尺度必须单独定义并核对。边长 0／1、最小包围方形、整数平移、奇偶方形、上确界和最终常数另立阶段；不把 n 与 n+2 静默等同。
- **保持当前主线边界：**本合同不接入 CMST/FSS，不增加恢复尾或有限性假设；即使全部连接完成，仍不能宣布 `τ(n)=Θ(n²)` 已形式化。
