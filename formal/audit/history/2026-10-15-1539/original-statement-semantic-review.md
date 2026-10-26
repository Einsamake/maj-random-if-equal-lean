# 原始问题尺寸、目标与最坏期望：独立 AI 语义审阅

审阅日期：2026-10-15。审阅者为未参与本阶段 Lean 证明编写的 AI 子代理 `/root/original_statement_audit`。本报告不是人类专家认证，也不是对完整二次主定理的验收。

## 当前结论与证据状态

已只读核对本阶段七个新模块的定义、量词、证明连接及原文含义；在下述范围内尚未发现具体语义漏洞。**统一构建与 `--trust=0` 公理审计已经成功，本子代理于北京时间 2026-10-15 15:42:47 独立逐源重算并核对了全部105个正式源码散列、实际源码集合、公开声明数和全部公理输出，均与成功记录一致。** 本子代理没有编写或修改 Lean 证明，也没有重复启动构建。

原始问题的**模型与优化对象**可以和本阶段定义对照；原始问题的**完整 Θ(n²) 命题**仍没有已完成的 Lean 证明。不能将这两个结论合并为“原始命题已经严格等价地证明”。

## 原文复核

本子代理独立读取了 [Fatès–Marcovici–Taati, arXiv:2101.12682v3](https://arxiv.org/html/2101.12682v3)（版本标记：2022-03-05）的 §1.2、§4.1、§4.2 式(36)及 Question 7.4。相关定义是：任意整数平移的半开方形最小边长；距离恰为 n 的确定性初态；到 H₂={全零,全一} 的首次恢复时间；其期望的最大值。规则为无限 Z² 上同步四邻多数、平局独立公平随机，不读中心状态。本文复核不涉及问题在其后是否已被公开解决。

本地精确合同见 [ORIGINAL_STATEMENT_CONTRACT.md](../../../ORIGINAL_STATEMENT_CONTRACT.md)。

## 六项语义核对

| 核对事项 | 当前源码中的实际对象与依据 | 判断 |
| --- | --- | --- |
| 原尺寸与有限参数 | `PerturbationGeometry.Fits` 允许任意整数平移和自然数边长；`diameter` 取最小边长；`original_side_sub_two` 及 `PerturbationNormalization.exists_normal_form_exact` 明示 N≥2 时有限参数为 N−2，真实边长为 N | 没有以 N+2 偷换原尺寸 |
| 恰 N 与至多 N | `OriginalRecoveryProfile.tau`、`normalizedTau` 的第二个上确界均要求 `distance = N`；归约中的代表 pattern 仍满足该等式 | 没有删除最小性义务；`Fits ... N` 单独只代表至多 N |
| 无限差异与有限背景 | `diameter` 无容纳方形时取 ∞；`finite_iff_exists_fits` 和 `diameter_ne_top_iff` 双向连接真实有限性；`finite_background_unique` 使用无限格排除两个有限背景；`opposite_diameter_top` 排除错误背景 | 有限背景唯一性是证明结果，不是额外假设 |
| 目标集合与正确背景 | `HomogeneousRecoveryTime.Homogeneous` 恰为两个常值配置；`synchronous` 为实际集合首达；通过固定容纳方形外始终保留背景值的点排除先到相反常值，得到 `synchronous_eq_background_of_finitePerturbation` | 不是仅把零首达重新命名为 H₂ 首达；相等性逐样本成立 |
| 无限恢复时间与期望 | 实际首达由 `ExtendedRecoveryTime.time` 未命中分支取 ∞；`ExtendedRecoveryExpectation.expectation` 用 `ENat.toENNReal` 的非负积分，∞保留为∞；平移、补、有限方形的期望等式均使用实际 law 等式 | 没有先假设恢复有限、积分有限或把∞转成0 |
| 最坏期望与最大值 | `tau_eq_normalizedTau` 以空间平移／背景补归约；`tau_attained_finite_pattern` 对 exact-N finite patterns 的非空有限集合用 `Finite.ciSup_mem` 取最大值，值域仍为 ℝ≥0∞ | 最大可实现不要求有限期望；满方岛目前只是非空及下界见证，没有被假设为最坏态 |

## 证明连接的具体检查

`expectedRecovery_finite_square` 先证明 H₂ 首达与零背景首达相等，再使用既有 `SquareGridLaw.synchronous_recovery_map` 的整个恢复时间 law；不只用某个时刻的边际概率替代整场或首达分布。其后期望等式由可测首达的 pushforward law 推出。

`tau_eq_normalizedTau` 的两个方向分别是：任意原初态存在保留 exact-N 的有限代表，故原优化不大于有限优化；任意 exact-N 有限代表的零延拓本身就是原优化允许的初态，故反向不等式成立。没有假设最大态对平移之外的任意变形保持期望，也没有把所有至多 N 的 pattern 无声并入 exact-N 集合。

`distance_zero_iff_homogeneous` 与 `tau_zero` 单独处理尺寸0。补读并审阅了第七个模块 `SmallDiameterRecovery`：边长1的容纳方形只有一个格点，四个邻点均为背景；方形外通过既有支撑不变量保持背景，因此一步后已到 H₂；exact-1 排除初态已在 H₂，得到逐样本真实首达恰为1。`expectedRecovery_eq_one_of_distance_one` 继而对概率测度积分得到期望1；`tau_one` 的反向见证是 `squareConfig 1`，不是空集合上确界。最后 `tau_attained_all` 分 N=0、1、N≥2，故每个自然尺寸的最大扩展期望均可实现。

**最大值存在不意味着最大值有限。** 对 N≥2，上述结论允许某个代表的期望和最大值同为∞，并未预设待证的概率尾界。

## 公理与内核证据

最终独立核对的机器可读记录见 [original-statement-independent-evidence.json](original-statement-independent-evidence.json)，含全部105个源码的重算散列、公开声明计数、验证和日志文件散列及精确范围。

| 项目 | 最终独立核对结果 |
| --- | --- |
| 统一分析验证记录 | `analysis-validation.json`，`2026-10-15T15:39:59.864188+08:00` |
| 分析工程 | 96个模块、1207条公开定理、97个正式源码；实际源码集合和全部散列均匹配验证记录 |
| 分析构建及公理输出 | 构建退出0；`lake env lean --trust=0 AnalysisAxioms.lean` 退出0；1207个互异公开声明均有且仅有一条公理结果；构建警告为空 |
| 分析工具链 | Lean 4.35.0-rc4；mathlib `54c01c3314d33d15d77893cbe4e0472ff26bb34d` |
| 核心工程 | 8个正式源码全部散列匹配；125条公开定理和1个模型定义，共126条公理结果；既有构建及 `--trust=0` 审计退出0，工具链为独立的 Lean 4.35.0 |
| 实际传递公理 | 两个工程都只出现 `Classical.choice`、`Quot.sound`、`propext`；没有 `sorryAx` 或自定义公理 |
| 新增阶段 | 7个模块、99条公开定理：Geometry 16、Symmetry 14、Normalization 6、HomogeneousRecoveryTime 33、ExtendedRecoveryExpectation 8、SmallDiameterRecovery 5、OriginalRecoveryProfile 17 |
| 既有基线 | `history/2026-10-15-1225/analysis-validation.json` 的89个证明模块全部保持原散列；新增7个模块，原文件中仅统一导入入口改变；旧记录未覆盖 |

对全部正式源码进行去注释后的独立文本检查，也未发现 `sorry`、`admit`、自定义 `axiom`、`unsafe`、`implemented_by`、`native_decide` 或 `debug.skipKernelTC`。文本检查与标准内核、传递公理输出共同作为证据；文本检查本身不代替内核验证。公理输出解析保留了 Lean 声明名中合法的撇号，未将这些声明遗漏计数。

这里核对的是主代理实际执行的成功构建及标准内核审计记录，并将它们绑定到当前源码；不是本子代理另跑了一次构建，也不包含工具链供应链的额外认证。

## 保留的主定理缺口

本阶段没有证明统一二次尺度的 FSS/CMST 上尾与下尾，也没有证明一般尺寸 N≥2 的最坏期望已有限或满足二次两向界；尺寸0、1的精确值是本阶段单独完成的特例。当前模型、真实概率 law、尺寸归约及最大值存在，都是后续定理的对象和连接；它们本身不是 Question 7.4 的完整形式化解答。

即使最终全部声明通过标准内核，严格结论也仅是这些已精确定义对象的定理成立；“独立 AI 审阅未发现问题”不等于“独立人类专家确认绝无漏洞”。
