# 原命题、假设和 Lean Kernel 独立审计

审计时间：2026-10-14，北京时间；末次补充依据 21:23:52 的统一验收。审计者为本轮新加入、未参与证明编写的独立 AI 子代理 `/root/independent_formal_audit`。本审计不修改任何证明源码，不构成人类专家评审或外部认证。

## 逐项结论

| 用户要求 | 审计判断 | 实际能够确认的范围 |
|---|---|---|
| 原始数学命题与 Lean 定理严格等价 | **未完成，不能签署** | 原模型的若干规则、确定性和概率辅助结论已经对应；尚无完整 `τ(n)=Θ(n²)` Lean 主定理，缺少整条概率及参数连接，因此不存在可供等价核验的最终定理 |
| 没有未经证明的不可信假设 | **对已验收证明对象通过；主定理依赖仍未闭合** | 含本轮 21:23 统一审计的已验收公开定理，传递公理依赖仅为 Lean/mathlib 通常使用的三项基础公理；79 份正式源码未见占位、自定义公理或内核绕过。通用引理的显式条件仍是条件，不能视为实际 CA 已满足 |
| 标准 Lean Kernel 成功验证 | **两工程全部公开声明的低信任统一检查通过，有限 PW 另有独立复查** | 分析 886 条、核心 125 条定理及 1 个模型定义的 `--trust=0` 公理审计退出 0；本子代理另运行有限 PW 四个最终接口及其全部导入闭包，退出 0 |
| 独立专家确认目前形式化没有漏洞 | **尚未获得独立人类专家确认** | 本次提供独立 AI 的代码和语义审查。在明确审查范围内未发现实质漏洞，但不能声称绝对无漏洞，亦不能冒充独立人类专家签署 |

## 一、审计基线及直接证据

冻结基线为 [20:56 分析验收快照](history/2026-10-14-2056/analysis-validation.json) 记载的 **2026-10-14 20:56:32.633577 +08:00**：64 个分析模块、842 条公开定理、65 份正式分析源码。核心另有 7 个模块、125 条公开定理和 1 个模型定义、8 份源码，见 [同阶段核心验收快照](history/2026-10-14-2056/core-validation.json)。后文新增阶段单独补充，旧数字不指向会更新的当前文件。

本审计实际重新计算全部基线源文件 SHA256：分析 65/65、核心 8/8 与原验收记录匹配。独立解析公理日志得到分析 842 个不重复公开声明输出、核心 126 个声明输出（包含上述模型定义），与验收范围相符。扫描去除嵌套注释后的全部这些源码，没有 `sorry`、`admit`、自定义 `axiom`、`unsafe`、`native_decide`、`implemented_by`、`debug.skipKernelTC`；另未发现待审查的 `elab`、`run_elab`、宏或外部归约证明构造。证据保存在 [独立基线核对 JSON](independent-semantic-baseline-2026-10-14.json)，核对脚本为 [independent_semantic_checks.py](independent_semantic_checks.py)。

基线分析验收 JSON 的 SHA256 为 `f5bdc9d2d1f45e37d9f4fcd1b996e2c4499d714a1c0ae614a12e7a03912a8cb3`。此哈希用于标定本次冻结记录；后续工程继续时当前验收文件可以更新，不能据本报告自动认证后加证明。

本次同时看见 `ClockEndpointMean`、`RankScanEmbedding`、`SquareScanKernel`、`ClockCensoringKernel`、`RankClockCensoring`、`ClockRecoveryComparison` 六个新增文件。它们在 20:56 冻结基线以外，本报告末尾按 21:23 新验收记录单独补充。

## 二、原命题与实际定义的对应

直接读取 [Fatès–Marcovici–Taati 原文 v3](https://arxiv.org/html/2101.12682v3) 的 §1.2、§4.1、式 (36)、Proposition 4.1 及 Question 7.4。该版本日期为 2022-03-05：模型在 `ℤ²` 上同步更新，仅使用四个相邻格，平局独立公平抽样；原问要求精确恢复速度，并猜想二次。`τ(n)` 是扰动直径恰为 `n` 的确定初态的最坏期望恢复时间；此“直径”指最小包围整数方形的边长，不是错误格数。合法空间包含全零和全一两态。

逐项核查结果如下。

| 原数学对象 | 实际 Lean 对象 | 结论与边界 |
|---|---|---|
| 四邻、排除中心、平局公平 | 核心 `Majority.update`、`Grid.update`；分析 `SquareSpin.rule`、`ones_eq_four_inputs`、`FairMarks.fair` | 规则吻合。分析边界外输入固定 false，阈值始终为 2，不是只按内部邻居数取多数 |
| 同步更新 | `Grid.synchronous`、`SquareDynamics.synchronous_succ` | 具体确定性递推吻合。同步与交替拆分在固定共同标记场下成立；该恒等式本身不声称两条轨迹独立 |
| 真实独立公平随机标记 | `FairMarks.markMeasure`、`marks_independent`、`ClockExecutionLaw`、`ClockSelectedMarks` | 真实乘积测度及 clock-only 注入选择 law 已证明。不能扩张成读过标记后的任意自适应选择 law |
| 无限格有限扰动 | 核心 `Grid.Site = Int × Int`、`Supported`、`synchronous_supported`；分析 `SquareTasks.Vertex n = Fin (n+2) × Fin (n+2)` | 支持保持和实际有限方形已分别存在；最终无限格概率模型、平移/颜色对称、有限方形 law 与原尺寸参数仍须显式连接 |
| 原方形尺寸 `n` | 核心 `Inside n` 为半开边长 `n` 方形，分析边长为 `n+2` | 不能将分析的 `n` 直接作为原命题的 `n`。最终须处理重参数化、尺寸小例及“恰为 n”与“至多 n”的最坏初态关系 |
| 首次恢复时间及无穷值 | `BipartiteDynamics.FirstZero` / `firstZero`；`ExtendedBlockTail` 使用 `ℕ∞` | `firstZero` 仅在提供有限吸收见证时定义；扩展块尾允许 `∞` 并由尾假设推出有限性。当前尚无完整实际 CA 的可测 `ℕ∞` 恢复时间、重启和期望主链 |
| 最坏期望的二次上下界 | 尚无完整 Lean 最终声明 | 因而原命题严格等价验收未通过。辅助定理数量不代表完成比例 |

这里的“未完成”是接口和结论尚缺，不表示已经核验的辅助命题存在矛盾。

## 三、是否存在核心结论偷渡

重点逐行核查 `SquareAttractivity`、`SquarePWMeasure`、`SquarePWDrop`、`SquarePWCensoring`，以及实际标记、有限字执行、时钟尾和扩展期望接口。

**有限字 PW 最终接口没有把密度演化、删更新不等式或概率 law 当作输入。** `warmWord_censoring` 只要求 `β≥0`、`short.Sublist full` 和实测试函数单调，从最大态比较真实有限热浴字。其密度演化由真实 Gibbs 详细平衡推导；最大态 Dirac 相对正 Gibbs 质量的密度单调已证明；单步下降使用两点纤维的可比性及 Dirichlet 恒等式。删字归纳中的条件被前述引理实际解除。

`actualMajorityWordMean_censoring` 通过固定有限字的零温极限传递，未交换无限时间或无界随机字极限。`chronological_fair_execution_censoring` 和 `freshExecutionLaw_censoring` 另要求完整事件身份 `Nodup`；这是独立公平事件标记的合法结构条件，允许同一站点重复更新。传入 `freshRun` 的字是时间正序字的 `.reverse`，与其 newest-first 约定一致。最终结论为期望/分布序，不是共享同一随机标记时的逐样本删更新不等式。

以下条件必须继续保留，不能因名称含“actual”“recovery”而忽略：

- `ExtendedBlockTail.lintegral_le_two_blocks` 显式接收几何尾 `hTail`。它是通用“尾界推出期望界”工具，不是实际恢复尾已证。对实际 CA 的尾与重启仍未实例化。
- `firstZero`、`finite_absorption_comparison` 显式接收有限吸收见证。当前文档将其列为有限见证下的确定性比较，解释准确；不能以它先验认定实际恢复时间有限。
- `ClockStoppedResidual.clock_wait_hasLaw` 对任意 `R` 要求停时、逐样本非负、几乎处处有限。这些是该泛型定理的公开条件。实际任务的 `task_delay_hasLaw`、`task_delay_indep` 已使用已证 readiness 结构解除这些条件。
- 较早的 `SquareTaskTail`、`ClockMaximum` 等保留 law/独立性输入的通用中间命题，不构成自定义公理；`ActualClockTail.actual_square_eight_tail` 的最终实际方形接口不接收这类概率结论。实际 rank 尾亦只要求正阈值及模型参数。
- `SquareGibbsLaw` 使用有限实质量而非 `Measure` 包装，已证明正性与质量和为 1；PW 最终从质量为 1 的最大态出发。`FiniteWordKernel` 的积分空间有限且为概率测度，实际执行积分等式不靠“不可积时积分默认为零”取得。

在上述审查范围内，没有发现把待证主结论当作已验收最终接口的输入。**CMST/FSS、实际恢复比较/重启和最终期望结论仍是未完成工作，不能以自定义公理或作为参数加入后声称原命题完成。**

## 四、标准 Kernel 和公理复核

已实际核对本地编译器版本：

- 分析：标准 `Lean 4.35.0-rc4`，commit `c29b6dda4f7c20e3eeaa717c4e565663c5cfa364`，Release，非项目自制内核。
- 核心：标准 `Lean 4.35.0`，commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，Release。
- 分析 mathlib HEAD：`54c01c3314d33d15d77893cbe4e0472ff26bb34d`。

原基线的 `lake build` 及 `lake env lean AnalysisAxioms.lean` 退出均为 0；所有公开定理均有对应输出，仅出现 `Classical.choice`、`Quot.sound`、`propext`。这是接受 Lean/mathlib 标准基础公理的结论，不应称为“完全无公理”。公开定理的 `#print axioms` 检查是传递的，使用到的私有辅助证明不会因此逃过公理依赖核查。

本审计新建的 [IndependentSemanticKernelAudit.lean](IndependentSemanticKernelAudit.lean) 没有新增数学声明，只导入有限 PW 并打印其四个最终接口的类型、公理。实际执行：

```text
工作目录：<workspace>\formal\analysis
工具链：formal\.tools\lean-4.35.0-rc4-windows\bin
lake env lean --trust=0 ..\audit\IndependentSemanticKernelAudit.lean
```

**退出 0，用时 43.6509288 秒。** 根据该二进制 `--help`，信任级别 0 不信任宏，并类型检查全部导入模块。此复核覆盖 `SquarePWCensoring` 的 **51 个本地分析模块导入闭包**及其外部依赖，未重新启动全部工程构建，也没有把其范围夸大成所有项目文件的独立低信任复查。四个最终定理的传递公理仍仅上述三项。完整输出见 [独立 Kernel 日志](independent-semantic-kernel-2026-10-14.log)。

该标准分析 `lean.exe` 的实测 SHA256 为 `7a021c48e75e886737a5c7aecb117a804d0169ba130d5d2cf5a234d9a199eae1`；核心 `lean.exe` 为 `ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea`。本审计核对运行版本与记录这些本地二进制的身份，没有另行完成编译器供应链证明。

原构建保留九项 dependency checkout 本地改动提示。本审计另外只读检查这九个依赖的 `git status --short`，均未返回修改行；未重置或修改依赖，也不删除原警告记录。

## 五、目前可签署的精确表述

> 对本报告标定的已验收源码（含末节 21:23 新验收），独立 AI 审查未发现所检查辅助定理的实质语义漏洞；两工程统一构建和全部公开声明的传递公理审计经标准 Lean `--trust=0` 通过，有限字 PW 的四个最终接口及导入闭包另有独立成功复查。完整原问题尚未获得 Lean 主定理，严格等价和独立人类专家确认仍未完成。

后续应在最终主定理出现后，另验收原尺寸/有限扰动/最坏初态、扩展恢复时间、真实概率测度、上下界及所有量词，再由独立人类专家审读原命题到 Lean 定义的对应。Kernel 验证证明对象的类型正确性，不能替代该数学语义对应。

## 本轮新增证明的验收补充

主代理完成统一验收后，本审计再次只读核对 [当前分析验收](analysis-validation.json)、[当前核心验收](core-validation.json)、对应公理日志及全部源码；另存 [最终独立核对 JSON](independent-semantic-final-2026-10-14.json)，没有覆盖原冻结基线核对文件。

- 分析：**2026-10-14 21:23:52.886183 +08:00**，70 个模块、886 条公开定理、71 份正式源码，统一构建和全部 `#print axioms --trust=0` 退出 0。
- 核心：**2026-10-14 21:18:34.078751 +08:00**，7 个模块、125 条公开定理和 1 个模型定义、8 份正式源码，同样统一构建和 `--trust=0` 审计退出 0。
- 本子代理实算 **79/79** 份源文件哈希与新验收完全匹配；公理日志实际有分析 **886/886**、核心 **126/126** 个不重复声明输出，仅上述三项标准公理。全部正式源码的禁止构造和额外元编程扫描仍无命中。
- 新分析验收 JSON 的 SHA256：`bb0e958cbdb9e2447fea64c00867d2f00e0873b99c7495d641f3be5264d1d47d`；新核心验收 JSON：`f01795bc4ff47bbca4c29c4dca23d4e1cef545709144b99bc3ca987f6ea5bcb1`。

本轮增加 6 个模块、44 条公开定理；本子代理已逐文件阅读六模块，新增数与统一验收逐项核对如下。

| 模块 | 新增公开定理 | 语义审查结论 |
|---|---:|---|
| `ClockEndpointMean` | 6 | 在真实独立身份标记上积分，Fubini 连接随机时钟端点与 cold-word 平均；有限配置观测确保可积，不要求随机字长度有界 |
| `RankScanEmbedding` | 9 | 真实正 rank 槽按原顺序补齐为全颜色扫描，并推导 Sublist；rank 上界在中间接口中公开，随后由实际 rank 事件解除 |
| `SquareScanKernel` | 9 | 同颜色不同格更新由具体规则交换；冷核平均对层内枚举顺序不变，允许完整枚举随 clock 样本改变 |
| `ClockCensoringKernel` | 5 | 实际已完成任务给出真实选中字；AE regularity 已证明，最终删更新比较不接收 law 或 Sublist 作为概率输入 |
| `RankClockCensoring` | 6 | 实际 rank 失败事件的补集给全扫描到实际字的 PW 比较；反方向由任务完成得到，方向与最大态删更新原则一致 |
| `ClockRecoveryComparison` | 9 | 实际端点非零指标单调且在 `[0,1]`，真实乘积测度下的两向端点概率加上调度失败项；最终不接收欲证概率界 |

精确地，令 `Cₙ(t)` 为从最大态出发的实际 clock/mark 端点非零概率，`Sₙ(c,m)` 为同一固定零边界方形的 `m` 次完整颜色扫描后的 cold-kernel 非零概率。最终 `two_way_scheduling_scale n c k` 给出

```text
tₖ = 8 log(2) (k+1),   qₖ = 128(k+1),
εₙ,ₖ = (6/5) (n+2)² 2^(-(k+1)),

Cₙ(tₖ) ≤ Sₙ(c,k+1) + εₙ,ₖ,
Sₙ(true,2qₖ) ≤ Cₙ(tₖ) + εₙ,ₖ.
```

该实际接口仅输入 `n,c,k`，中间积分所需单调性、可积性、事件可测性及调度尾已实际证明。本审查没有发现 reverse 约定、删更新方向、零 rank 阈值边例或 AE fallback 的实质问题。

**这些是有限方形、最大初态、实际端点非零概率的比较。** 不能直接称为原无限格首次恢复时间的尾界或最坏期望的 `Θ(n²)`。首次恢复时间/无穷值、原扰动尺寸与方形概率 law、CMST/FSS、真实重启和最终上下界仍未闭合；严格等价和人类专家确认的结论因此不变。
