# 实际保护域阶段：独立 AI 语义审阅

审阅者：`/root/modified_clock_independent_audit`。日期：2026-10-16。本代理未参与本阶段 Lean 证明编写，只读正式源码；未启动重复构建。本报告不构成人类专家认证。

**具体保护集合、实际时钟端点比较及冻结源的统一证据已独立核对，未发现所审范围内的具体漏洞。完整二次主定理仍未完成。**

## 原始对象与来源边界

直接读取了 [CMST v2 原文](https://arxiv.org/html/1007.3599v2) §3末“More notational conventions”和 §8 Definition 7(e) 及其后的停止规则。离散边界在集合外，由与集合内某点相距一个格距的格点组成；内域为闭 L¹ 菱形，半径 `(9/10)L`，实际保护集合是 `D∪∂D`。

源码中的实际四邻与 Z² 欧氏距离1的四种整数坐标差完全对应。该来源只界定模型语义，没有被作为 Lean 公理或概率界输入。准确定位也保存在 [原文核对记录](clipped-protected-geometry-source-note.md)。

## 逐项语义核对

| 对象 | 独立核对结果 |
| --- | --- |
| 全格点内域 | innerDiamond 虽用有限坐标方形过滤构造，但 mem_innerDiamond 实际证明与全 Z² 的 `10*(abs x+abs y)≤9L` 等价，坐标限制已由该不等式推出。不是把内域任意截断后沿用原名称。 |
| 原来的非严格半径 | mem_innerDiamond_iff_real 证明与实数半径 `(9/10)L` 的非严格不等式等价；没有实数除法、自然数除法或严格边界的误换。 |
| 外边界 | outerBoundary 是 innerDiamond 各点的真实四邻并集，再减去 innerDiamond。mem_outerBoundary 同时要求点在 D 外且有 D 内四邻；boundary_disjoint_inner 核对其确为外边界。 |
| 完整保护集合 | protectedSites 定义为 D 与外边界的并集。通过非零点向原点移动一步、L¹ 范数恰减1的实际邻点，证明 protectedSites 恰为既有 boundaryBand 的所有格点，即 `10*norm1≤9L+10`。这不是仅证明包含于任意放大的替代保护域。 |
| 小尺寸及支撑 | protectedSites 非空由原点得到；包含于实际 clippedDomain 的定理保留 `L≥1`。L=0 的外边界确不在单点剪角域，因此未做错误延伸。本轮概率实例统一保留更强的 `L≥40`，与后续方块计数范围一致。 |
| 初态与清理 | 初始剪角域实际包含保护集合，故对应负自旋为 true。初态 cleanup 不变使用上一阶段已证明的剪角域稳定性，再推出 cleanup 后仍包含保护集合；没有将初始稳定性或保护结论作为未经证明的条件。 |
| 四向方块 | directedBlock_control 将实际保护点接到既有四向块的域内包含、精确基数 `(L/20)^2` 及实数下界 `L²/1600`。所得仍是几何格点计数，不是“退出前这些点已经被删除”。 |
| 实际 finite vertices | protectedVertices 过滤的是真实 finite square 顶点，其 recenter 像精确等于 protectedSites。非空、包含于实际 clippedVertices、全部受保护自旋为 true 当且仅当完整 protectedSites 包含于集合 S，均已证明。没有遗漏外边界顶点或添加虚构顶点。 |
| 原全负初态 | 原有限全 true 配置的 occupied 集合之 recenter 像恰为整个 centeredSites。结合 clippedDomain 的实际包含，可将上一阶段通用不同域比较实例化为原整方岛全负初态与真实剪角全负初态。 |
| 真实概率实例 | 原 ClockExecutionLaw.endpoint 在物理 t 全 false 的概率，被同一真实 clock/fair-mark product measure 下剪角改造 endpoint 失去具体保护顶点的概率控制。第二种表述又由 protected_present_iff 严格改写为实际 `D∪∂D` 的集合缺失。没有任意 I、外加目标 law、尾界或漂移结论残留为本阶段概率命题参数。 |
| 退出索引 | protectedExitIndex 使用实际 clippedDomain、其全负初态及具体 protectedSites；保留 ℕ∞。正性只来自第0事件索引的初始保护，不预设未来必然退出；与原 rawRecoveryIndex 比较的方向是 `exit≤recovery`。 |
| 索引与物理时间 | 出口正性及索引比较仍是确定性事件索引结论。物理 t 的概率命题使用真实 bounded-time clock word，不把索引等同于物理时刻。源码没有对所有异常时钟样本声称 t=0 端点逐样本恒等于初态。 |

## 冻结源及独立证据

统一验收时间：`2026-10-16T23:29:16.684465+08:00`。独立复核完成于 `2026-10-16T23:30:24.967942+08:00`，记录在 [protected-domain-independent-evidence.json](protected-domain-independent-evidence.json)，SHA256 为 `2e713b719cb1d352962eb460f9a051fcb36d705beb0516321818571049ec33d8`。

| 新模块 | 公开定理 | 受审命名声明 | SHA256 |
| --- | ---: | ---: | --- |
| ClippedProtectedGeometry | 23 | 28 | `d809d52a894b9adebd1ca33a2db3ea26489d9a4a31f13b643947c70ffd2980ea` |
| ProtectedDomainClockComparison | 11 | 14 | `c1e50fd47831b88d2cd285c278b6a5300747d1f7a2b059e670b74e6572d10efd` |

- 实际分析工程为107个证明模块、1445条公开定理、108份正式源码；与统一验收的路径集合和全部 SHA256 精确一致。
- 统一构建与标准 `lake env lean --trust=0 AnalysisAxioms.lean` 的实际日志均有退出码0；1445个互异公开定理的源码声明、审计指令及实际公理输出集合完全一致，名称中的合法撇号被完整保留。
- 42个新命名声明的单独标准 trust=0 审计也实际成功，日志有退出码0。包含两份源码中的公开定理、定义及 Site/Vertex 别名；源码名、审计指令、实际输出、验收 JSON 的声明集合与源散列均独立匹配。
- core 的8份正式源码与旧成功验收的散列一致；125条定理及1个模型定义共126项旧公理输出完整。core 沿用其独立 Lean 4.35.0 工具链成功记录，没有宣称本轮重新构建。
- 合计116份正式源码、1571项全局公理输出。分析仍为 Lean 4.35.0-rc4，记录的 mathlib 固定提交为 `54c01c3314d33d15d77893cbe4e0472ff26bb34d`。
- 相对 `history/2026-10-16-2300`，原105个证明模块散列全部未变，仅统一导入入口变化；新增2模块34条定理，无删除源码。
- 去注释文本扫描未发现占位、自定义 axiom、unsafe、native_decide、implemented_by 或 debug.skipKernelTC。实际传递公理只出现 Classical.choice、Quot.sound、propext；没有 sorryAx 或自定义公理。
- 当前构建保留一项环境警告：batteries checkout 存在既有本地修改；没有新的 Lean 源码警告。该事实已写入独立 JSON，没有将其隐藏为“完全无警告”。

上述核对独立重算全部当前源指纹及声明集合，但不重复构建，也不冒称进行了工具链供应链认证。

## 仍未验收的内容

本阶段关闭了此前一般保护集合 I 的具体化义务，但没有证明 Good 的简单轮廓、周长约束、角点分类、更新不变性或首退出已删面积。2-core 稳定与方块基数本身仍不能替代这些义务。

具体的确定性 first-loss index 尚未与真实物理首次退出逐路径相连；实际停止 clock 整过程 law、生成元及相应观测量演化也未由本阶段得到。不能将未停止端点概率实例称为完整停止链验收。

CMST/FSS 的二次尺度概率上下尾、一般扩展期望有限、最终统一常数及完整 `τ(N)=Θ(N²)` 主定理仍未完成。本次仅对上述具体阶段做独立 AI 语义与证据核对，不构成人类数学专家签署。

