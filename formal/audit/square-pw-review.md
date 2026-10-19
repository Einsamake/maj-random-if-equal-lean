# 具体方形有限字 PW：独立语义复核

日期：2026-10-14，北京时间。审查者 `/root/proof_retro_review`。

本次只读审查 `SquarePWMeasure.lean`、`SquarePWDrop.lean`、`SquarePWCensoring.lean`，并追读原有 `ZeroTemperature`、`FiniteWordKernel`、`ClockExecutionLaw` 的真实定义和调用接口。审查者实现过单独的 `SquareAttractivity` 模块，因此不将该模块的自查称为独立审查。没有修改这三个被审查模块，也没有启动重复总构建。最终构建、公理、哈希统一验收由主代理完成；本文只报告源码语义核对，不替代 Lean 内核或外部数学审阅。

## 结论

在以下明确范围内，未发现语义、比较方向或时间顺序缺口：实际有限方形、固定外零边界、`β ≥ 0`、全 true 最大初态、任意有限时间正序站点字及其 Sublist、单调实测试函数。最终接口给出真正的有限字热浴删更新不等式，并通过既有有限字零温极限接到实际独立公平标记执行积分。

这里不是把 Gibbs 平稳性或若干单调性引理当作 PW；`warmWord_censoring` 已消解最终结论中的单调密度前提。随机时钟选择、恢复事件、CMST/FSS、重启及完整 CA 二次时间主定理不在这一接口内。

## 核对一：正向质量演化与反向测试函数的次序

`SquarePWMeasure.step β v ρ g = Σ_f ρ(f) K_v(f,g)` 是真实单站核的正向质量更新。`runMass (v::rest) ρ = runMass rest (step v ρ)` 先执行 v，再按 rest 执行，没有把时间反转。

现有 `ZeroTemperature.warmWord β (v::rest) φ = warmStep β v (warmWord β rest φ)` 则是同一时间正序轨迹的反向测试算子：先对后缀终态测试求值，再经第一个更新取期望。二者的方向不同是正常的对偶，`expect_runMass` 用真实有限和及 `expect_step` 证明

`expect (runMass β word ρ) φ = expect ρ (warmWord β word φ)`。

没有把同一站点的非交换更新擅自反序，也没有要求站点字无重复。

`density_step` 使用原有实际 Gibbs 正质量和详细平衡，逐项证明更新后密度等于 `warmStep` 作用旧密度。它不是单纯用平稳性猜测的恒等式：分母用 `mass_pos` 确保非零，交换核方向用实际详细平衡，目标自变量 g 对应当前配置。这样后续密度闭包使用的确实是正确的热浴算子。

## 核对二：单步降序并不偷用 PW

`SquarePWDrop` 直接证明可逆 Dirichlet 恒等式：两倍期望下降等于所有有序配置对的有限和。每项系数为实际非负 `π(f)K_v(f,g)`，其余部分为

`(d(f)-d(g)) * (φ(f)-φ(g))`。

若核支持该转换，f、g 在 v 外完全相同，而 v 为 Bool，故两者在点态配置序下可比较。单调 d 与 φ 的差同号；不支持的配置对核为零。因此每项非负，得到 `expect(step ρ)φ ≤ expect ρφ`。

这个单步命题假设的是旧 Gibbs 密度单调，且不要求 β 非负。该加强没有问题：可逆性、核非负和单站 Bool 可比性对任意实 β 成立。真正从多步最大态演化保持密度单调时仍明确使用 β≥0 的 attractivity，没有偷换温度条件。

该代数命题甚至不需要 ρ 归一化；最终应用从真实 `topMass` 开始，已有 `topMass_nonneg`、`sum_topMass`、`step_nonneg`、`sum_step` 支持其真实概率解释。泛型引理范围较宽不造成最终结论的概率前提缺失。

## 核对三：最大态密度与 Sublist 归纳方向

`topConfig n := fun _ => true` 是标准点态 Bool 序的最大配置。`topMass` 是只在该配置取值 1 的 Dirac 质量。Gibbs 质量处处正，所以密度在非最大态为零，在最大态为正；若 f 是最大态且 f≤g，则 g 也是最大态。`topMass_density_monotone` 正确证明此事实，没有错误要求 Gibbs 质量自身随配置单调。

`censoring_from_density` 对 `short.Sublist full` 归纳，其两个关键分支正确：

- `cons` 表示完整字多一个头部更新 v。先用归纳假设将完整后缀删到短字，起始质量为 `step v ρ`；再将短字测试推回为 `warmWord short φ`，用其单调性对头更新应用单步下降；得到“完整字期望≤删后短字期望”。
- `cons_cons` 表示两个字保留相同头更新；共同更新后以已证明的单调密度继续归纳。

两处分支都从 β≥0 的真实热浴单调性推导新密度或后缀测试单调，没有把 PW 作为归纳输入。最终 `warmWord_censoring` 使用最大态已证密度单调，所有密度前提在最终定理中消失，只保留 β≥0、Sublist 和测试函数单调。

比较方向是完整字终态随机序较小、删选字较大。它没有扩大到任意确定初态；后者通常不成立。

## 核对四：零温传递

`actualMajorityWordMean_censoring` 使用原有两个固定有限字的真实 β→+∞ 极限，再以 `eventually_ge_atTop 0` 提供温度最终非负条件，最后用闭序极限传递不等式。

没有在 β=∞ 时假设 Gibbs 质量仍处处正，没有把极限概率 law 作为输入，也不涉及随机字长度的统一上界、概率与温度极限换序或支配收敛。任意单调实函数在当前有限状态空间上均可使用，不需要另加非负测试函数条件。

## 核对五：真实标记积分与事件反序

原始 `ClockExecutionLaw.freshRun events ξ initial` 执行的是 `events.reverse`，因为其参数约定为 newest-first 身份字。现在最终定理将真正时间正序 full 传为 `full.reverse`，由此执行次序为 `full.reverse.reverse = full`，正确。

`chronological_fair_execution_censoring` 通过既有 `FiniteWordKernel.chronological_fair_execution_mean`，把两侧各自长度的公平积积分严格化为 `actualMajorityWordMean (word.map Prod.fst)`。`Sublist.map` 保留站点时间顺序；事件身份 `full.Nodup` 给出短字身份无重复。没有要求投影后的站点字 Nodup，因此同站点可以合法多次更新，且对应不同身份的独立硬币。

若同一事件身份重复，`freshMarks` 会用 idxOf 复用其首次坐标，不能读作独立重采样。最终接口明确保留 `full.Nodup`，正好排除这一风险。

`freshExecutionLaw_censoring` 对真实 pushforward 执行测度应用原有积分等式，同样先反序再双反序还原，方向一致。两侧使用各自的独立公平向量积分，定理没有主张同一随机标记样本下逐路径“多更新必更快”。

## 边界与应保留的说明

- Sublist 的空字、相等字和站点重复都在全称声明及归纳中覆盖；未发现隐藏的正长度假设。
- β=0 在非负温度范围内；负 β 的完整删字结论没有被宣称。
- 外边界、四邻场和真正热浴 logistic 核通过现有 SquareGibbsLaw 连接，无替换成内部邻居可变度多数的迹象。
- 这些定理只给确定有限字的分布比较。将随机 clock-only 字逐纤维使用并积分，仍是后续工作；不能由本阶段跳称实际恢复事件比较已闭合。
- 本审查读取的三个源内没有发现 `sorry`、`admit`、自定义 `axiom`、`unsafe`、`native_decide`、`implemented_by`、`skipKernelTC`。这仅是直接源码扫描；传递公理依赖仍须以统一 `#print axioms` 输出验收。
- 辅助定理数量不表示完整 CA 主定理的完成比例。

## 审查源码指纹

以下为本次只读快照；若源码改变，主代理应核对变更而非无条件沿用本报告。

| 源码 | SHA256 |
|---|---|
| SquarePWMeasure.lean | `9375c7d10e87322640ad8bf355b6da7c105eb494feef36b5a1a33c766975da29` |
| SquarePWDrop.lean | `a5491e96b2edfa8ea0efdaa9ecbc2dbfff784b922796ea01da7eb1b06b31c062` |
| SquarePWCensoring.lean | `336d2d14762c2d00e0352f3e514852033dfa7808cc9bd96654333701eca0a994` |

未发现需要退回修改的具体语义问题；最终是否达到本阶段合同，仍由实际构建、公理审计与上述最终接口共同决定。
