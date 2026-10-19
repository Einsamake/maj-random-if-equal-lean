# 有限方形随机动力学与扩展恢复时间：独立语义复核

日期：2026-10-14，北京时间；最终核对时间 21:50:59。复核者为未参与本轮证明编写的独立 AI 子代理 `/root/independent_formal_audit`。本次只读审查证明源码，写本报告及获授权的核对证据 JSON；不重跑重复构建，不改 Lean 证明。

## 结论与范围

本轮逐文件审查 `SquareRandomDynamics`、`ExtendedRecoveryTime`、`SquareScanOrder`、`SquareRandomComparison`、`SynchronousClockComparison`、`SquareRecoveryTime`，未发现以下重点接口的实质语义漏洞。最终统一构建、公理审计及源指纹已按本报告末节实际核实通过。

本轮对象是边长 `n+2`、固定外零边界的实际有限方形随机过程，以及允许 `∞` 的首次全零时间。它比此前纯端点比较多了真正的有限方形恢复时间，但**仍不是原无限 `ℤ²` 最坏期望恢复时间 `τ(n)=Θ(n²)` 的完整定理**。独立 AI 审查不等于独立人类专家认证。

## 逐项核查

| 检查项 | 实际源码与推导 | 判断 |
|---|---|---|
| 实际独立公平随机源 | `SquareRandomDynamics.measure` 是事件身份 `(site,time)` 上的真实无限公平乘积；不是带 law 参数的任意过程 | 通过 |
| 时间 0 未被更新使用 | 同步和交替递推在步 `t+1` 读取 `(v,t+1)`；`fixedWord_positive` 及两个 `eq_of_agree_positive` 证明修改时间 0 标记不影响任何轨迹 | 通过 |
| 首次更新颜色与 phase | `fixedWord n c count` 第一层更新 `c`，执行恰为 `alternating ... (!c)`；积分 law 对 phase 给扫描首色 `!phase` | 通过；没有差一颜色错误 |
| 同色批次与实际扫描 law | `execute_taskLayer_eq_checkerboard` 使用具体同色更新；每层身份唯一，跨层时间不同；实际无限标记积分等于已有 `scanMean` | 通过；允许站点跨层重复，未复用同一身份 |
| 两相位共享标记 | 同步与两种交替过程共用同一个样本；非零事件包含于两相位非零事件并集，随后仅使用并集界 | 通过；未假设两相位独立 |
| 首达时间保留无穷 | `ExtendedRecoveryTime.time` 在存在首次全零时取 `Nat.find`，从未到零时取 `⊤ : ℕ∞` | 通过；不先验假定有限恢复 |
| 零吸收与尾事件 | 泛型 `time_gt_nat_iff_of_absorbing` 明列吸收结构条件；具体 `SquareRecoveryTime` 从实际零态保持定理解除条件 | 通过；`{t<T}` 与时刻 `t` 非零逐样本等价，包含 `T=∞` |
| 可测性 | 实际轨迹每个时间切片可测；泛型首达有限点纤维由可数交并构造，`ENat.measurable_iff` 给首达可测 | 通过；无有限性或尾界前提 |
| 初态支配 | 具体更新在共同标记下单调，非零事件对配置递增；首达时间支配对较大过程的有限时间和 `∞` 分别处理 | 通过；最大初态支配不是用欲证恢复结论作输入 |
| 同步/时钟两向比较 | 由真实端点比较、相位并集界和最大态 PW 删掉首/末层得到，保持明确时间位移与因子 2 | 通过；不是逐样本同步/异步耦合排序 |

## 对关键方向和索引的独立复算

记 `Uₙ(k)` 为最大态同步过程在时刻 `k` 的非零概率，`Sₙ(c,m)` 为首更新色 `c` 的 `m` 层扫描非零概率，`Cₙ(t)` 为既有真实 clock/mark 过程端点非零概率。源码实际证明：

```text
Sₙ(c,k+1) ≤ Uₙ(k),
Uₙ(2q+1) ≤ Sₙ(true,2q+1) + Sₙ(false,2q+1)
           ≤ 2 Sₙ(true,2q).
```

第一条由“同步在时刻 `k` 为零，则每个交替相位在时刻 `k+1` 为零”的共同标记确定性结论得到。第二条首先是同一样本上的两相位并集，再以最大态 PW 分别删除一层：true 首色删末层，false 首色删首层后得到 true 首色。没有将两相位概率相乘。

结合既有真实 clock/scan 比较：

```text
Cₙ(t) ≤ Uₙ(k) + P(实际 k+1 层任务未在 t 完成),
Uₙ(2q+1) ≤ 2 Cₙ(t) + 2 P(实际计算 rank 至少 q).
```

在已验收的调度尺度 `tₖ=8log(2)(k+1)`、`qₖ=128(k+1)`，错误项 `εₙ,ₖ=(6/5)(n+2)²2^(-(k+1))`，其两个方向为

```text
Cₙ(tₖ) ≤ Uₙ(k) + εₙ,ₖ,
Uₙ(2qₖ+1) ≤ 2 Cₙ(tₖ) + 2 εₙ,ₖ.
```

`SquareRecoveryTime.synchronous_tail_probability` 将 `Uₙ(k)` 与真实同步 `ℕ∞` 首达尾严格相等连接，所用零吸收已经针对实际规则证明。最终 `SquareRecoveryTime.two_way_clock_tail n c k` 已直接以 `{η | k < T η}` 和 `{η | 2qₖ+1 < T η}` 两个真实 ENat 尾事件陈述上述方向，只有 `n,c,k` 输入，没有有限恢复、law、删更新或欲证尾界输入。这里没有把同步时刻 `k`、交替层数 `k+1` 或时钟物理时间混成同一时间变量。空字、时刻 0 和较大过程永不恢复的分支也没有被排除。

## 假设与边界

- 泛型 `ExtendedRecoveryTime` 的吸收性、可测性条件是公开且必要的结构条件，具体方形接口实际解除；它没有把有限吸收当作前提。
- `SquareScanOrder.scanMean_censoring` 保留 Sublist 作为通用中间条件；最终首/末层扫描比较由具体扫描字证明该条件，`SynchronousClockComparison` 最终不接收删更新不等式或 probability law。
- 非零概率的辅助积分恒等式对一般测度使用 `.real`。实际随机动力学的调用测度已证明是概率测度，不能把该通用恒等式扩张成任意无限测度的通常概率解释。
- 本轮标记 law 已在实际无限公平乘积上定义，交替积分对应扫描核。还没有以此自动完成原无限格 PCA 的条件转移律、任意有限扰动的嵌入和平移/背景对称。
- 当前首达时间是有限方形同步/交替过程的首次全零时间；时钟一侧仍使用已有真实端点非零概率。没有将时钟端点概率冒称为已经构造、验证的无限格连续时间首达时间 law。
- CMST/FSS 方岛深依赖、真实块重启及最终期望上下界不在这六模块的结论内。不能把辅助比较成功视为 `Θ(n²)` 已闭合。

## 最终构建及公理记录

已实际读取主代理完成的统一记录，随后由本子代理独立重新计算全部正式源哈希并核对公理输出。证据见 [square-random-recovery-validation.json](square-random-recovery-validation.json)。前一 21:23 基线已保存在 [历史验收](history/2026-10-14-2123/analysis-validation.json)，本报告没有覆盖先前独立审计或其指纹 JSON。

| 工程 | 实际验收时间（+08:00） | 公开定理及模型声明 | 源文件 | Kernel 记录 |
|---|---|---:|---:|---|
| 分析 | 2026-10-14 21:50:15.804344 | 951 条公开定理、76 模块 | 77 | build 退出 0；`lake env lean --trust=0 AnalysisAxioms.lean` 退出 0 |
| 核心 | 2026-10-14 21:18:34.078751 | 125 条公开定理及 1 个模型定义 | 8 | build 退出 0；`lake env lean --trust=0 audit/CoreAxioms.lean` 退出 0 |

本子代理实算 **85/85** 份源码 SHA256 与对应当前验收记录一致；分析公理日志 **951/951** 个不重复声明，核心 **126/126** 个声明，逐项对照生成的 `#print axioms` 清单，没有缺失。传递公理仅 `Classical.choice`、`Quot.sound`、`propext`。统一记录无占位或自定义公理；九条依赖 checkout 提示保留，没有正式源码警告。

本轮六模块新增 **65** 条公开定理，逐项为：`SquareRandomDynamics` 13、`ExtendedRecoveryTime` 10、`SquareScanOrder` 11、`SquareRandomComparison` 13、`SynchronousClockComparison` 5、`SquareRecoveryTime` 13。数目只标定核对范围，不是主定理完成比例。

当前分析验收 JSON 的 SHA256 为 `216d8b23fd8f1585c8637170019df1df4b58fc1702e71bfd7239b103e139f822`；核心验收为 `f01795bc4ff47bbca4c29c4dca23d4e1cef545709144b99bc3ca987f6ea5bcb1`。六模块完整源指纹保存在本节所链核对 JSON。

**可以确认：本轮有限方形实际随机过程及真实 ENat 恢复尾连接经过源码语义复核和标准低信任 Kernel 验证，在所审查接口内未发现具体漏洞。不能确认：原无限格最坏期望 `Θ(n²)` 已被形式化，或已经取得独立人类专家认证。**
