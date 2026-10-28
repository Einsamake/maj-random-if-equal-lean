# 二次恢复时间定理：公开先例与首创性核查

核查日：2026-10-26。对象是本项目已完成的数学结论及其完整 Lean 形式化。三路 AI 检索分工并交叉核对作者材料、后续引用和形式化代码，主代理复核决定性来源并综合判断。

**结论：截至2026-10-26，本轮没有检出同一模型二次阶结论或同题完整形式化的公开证明。现有证据支持把结果作为可能的新贡献提交审阅，但不足以认证“全球首创”。** 没有发现先例与证明先例不存在，是两件不同的事。尤其本轮未取得完整前向引文清单，也未核查未公开手稿。

## 查证的究竟是哪一个结果

目标是无限整数格上的同步四邻多数规则：不读取中心，平局逐格逐轮独立、公平地掷币。初态只是全白或全黑背景的有限扰动。N 是包住扰动的最小平移轴平行半开方形边长；先对硬币求首次恢复时间的扩展期望，再在尺寸恰为 N 的确定初态中取最坏值。

本地最终定理为

\[
\frac{N^2}{56623104000}\leq\tau(N)\leq664066N^2
\quad(N\geq786432000).
\]

这是渐近 Θ(N²)，上界单独对 N≥16 成立。[最终 Lean 源](../../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean)和[实际验收说明](../../formal/PROGRESS_2026-10-26_MAIN_THEOREM.md)固定了待比较的结论。不能以环面共识、异步物理时间、错误格数或平均初态的结果替代它。

| 要判断的主张 | 本轮证据允许的判断 |
|---|---|
| 这条数学结论此前是否已有公开证明 | 未检出匹配先例；尚不能证明全球无先例 |
| 是否已有同题完整机器形式化 | 未检出；代码检索也存在索引遗漏 |
| 证明所用工具是否都是首次发明 | 不是；多项关键工具有明确经典前身 |
| 本项目是否已取得全球最早公开优先权 | 未确立；首次公开时间与先例覆盖仍须补证 |

## 最有分量的文献证据

| 一手来源及日期 | 实际核查位置 | 对本项目的意义 |
|---|---|---|
| Fatès–Marcovici–Taati，2022，[作者期刊 PDF](https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf) | §1.2 p31；§4.1–4.2 pp53–56；Q7.4 p79 | 模型、尺寸和最坏期望与目标一致。Proposition4.1 给三次上界，Q7.4 猜测二次；正文把连续时间结果另列为例子 |
| [原论文 arXiv 版本记录](https://arxiv.org/abs/2101.12682) | v1：2021-01-29；v2：2021-11-11；当前最新 v3：2022-03-05 | 本轮未见在原论文新版本中补上解答；无更新本身不能证明题仍开放 |
| Marcovici，2025，[Cellular automata and self-organisation phenomena](https://marcovici.perso.math.cnrs.fr/Publications/Marcovici_ESAIM2025.pdf) | §3.2，期刊 p24 | 描述四邻公平平局规则，并仍回顾其扩展的三次上界，没有报告本题二次改进。不是对2026开放状态的正式声明 |
| [Taati 作者页面](https://siamak.isoperimetric.info/) | 页面注明更新于2026年9月；2025–2026出版物及预印本列表 | 未见本题新解条目；作者列表未必穷尽 |

这组证据比只搜索精确题名更有价值：原文明确提出问题，后来的作者综述仍沿用原来的界。但两者都不能排除其他作者在之后以不同术语解决。

## 最容易误认的先例，逐项对照

| 已读取或明确标出阅读边界的来源 | 为什么不能直接算作本题已解决 |
|---|---|
| Caputo–Martinelli–Simenhaus–Toninelli，2010预印本／2011期刊，[原文 §3.2 Theorem2](https://arxiv.org/html/1007.3599v2) | 已有二维方岛在二次尺度消失的匹配概率界，但每格由独立 rate-1 Poisson 时钟异步更新。将其迁移到原同步规则仍需证明 |
| Marcovici–Taati，2026，[Positive-rate PCA and IPS with stationary Bernoulli measures are rapidly forgetful](https://arxiv.org/html/2605.16904v1) | 要求严格正转移率与平稳 Bernoulli 测度。本题有确定输出和吸收态，不满足该正率前提；混合／遗忘也不是同一个恢复时间目标 |
| Marsan–Sablik，2024，[Strong stochastic stability of cellular automata](https://arxiv.org/html/2403.19932v1) | 核心是不变测度在持续噪声趋零时的稳定性，非指定同步规则的有限扰动恢复期望 |
| Gayral，2023，[博士论文](https://lgayral.pages.math.cnrs.fr/files/manuscrit.pdf) | 已检查原论文引用上下文和相关词命中，讨论扰动铺砌与重构，没有检出本题二次界；封面日期为2023-06-23，搜索引擎的抓取日期不作出版日期 |
| Swart–Szabó–Toninelli，2026-05-11，[Peierls Bounds from Toom Contours](https://link.springer.com/article/10.1007/s10959-026-01508-2) | 其中同名 symmetric majority 是含中心的五格确定多数；主要结论是小持续噪声下的稳定性标准。不是四邻公平平局的二次恢复时间定理 |
| Cirillo–Jacquier–Spitoni，2022，[Metastability of Synchronous and Asynchronous Dynamics](https://pmc.ncbi.nlm.nih.gov/articles/PMC9029560/) | 有限体积、正磁场、低温极限的亚稳态问题，参数、边界与时间极限均不同 |
| Poirier–Theyssier，2026 ALEA，[作者研究页](https://leo-poirier.eu/recherche/) | 已读页面和可检索定理摘录指向一维测度的 Cesàro 收敛。幻灯 PDF 获取失败，不能记作全文排除 |

没有把不同模型中的“quadratic”当作本题先例，也没有断言这些一般理论永远不能导出本题。上述判断只针对实际读到的定理和假设。

## 形式化先例查到了什么

检索覆盖公开 GitHub 代码／仓库、Lean、Coq、Isabelle、AFP 概率分类及相关论文。精确规则名、arXiv号和一些排斥过程关键词没有返回匹配代码；宽化检索找到了相邻工作。成功查询、返回条目及失败请求见[代码检索记录](novelty_formal_github_search_2026-10-26.json)和[独立形式化报告](novelty_formal_2026-10-26.md)。

实际阅读的近邻包括早期 Lean 元胞自动机与边界框架、有限单点 Glauber 热浴链、mean-field 速率／ODE，以及[Lean 三态多数共识](https://github.com/formal-dynamics/leanamics/blob/ef4b8d60657213d8345512dc46dd461e505398c6/undecided/Undecided/Majority.lean)。后者是有限完全图的三态随机采样协议，非本题二维规则。[AFP Negative Association](https://isa-afp.org/entries/Negative_Association.html)也是一般负相关理论，非本题消滴证明。

因此，不能把本项目称为“首个元胞自动机形式化”或“首个概率过程形式化”。“本题首个完整形式化”仍只是本轮未发现反例的主张。GitHub精确代码查询甚至未返回本项目，足见零结果不能证明没有实现。

## 方法的创新边界

- 排斥过程编码、热方程与负相关有经典来源。CMST 原文已经使用界面与排斥过程的联系；本项目用一二矩、能量衰减和 Chebyshev 得到足够的局部清空概率，不因此把这些工具改称新理论。
- [Peres–Winkler](https://arxiv.org/html/1112.0603v1)已证明单调系统的删更新比较，并比较更新方案。其§3显示的损失和适用对象不直接就是本题所需的最终同步吸收界。
- [Liu–Yin](https://arxiv.org/html/2111.04044v2) Lemma3.11 已给 Poisson 更新依赖链深度尾界，并明确追溯更早论文。时钟链估计本身不是本项目首次提出。

本项目在数学结果与形式化交付层面可具体主张的贡献，是把这些思想在原模型、原随机分布及原时间尺度下接成完整二次界，并自含形式化必要步骤。哪些专门引理或组合在数学上首次出现，仍需逐条与领域文献比较；机器核验不回答这项历史问题。现行形式化没有把完整 CMST／FSS 消滴结论作为外部假设。

## 公开时间与现存证据

本轮只读 GitHub REST 返回本项目当前为 **public**，而此前封存记录记载当时为 private。此次检索没有更改仓库可见性或内容。实际核查时刻与响应另存于[REST观测记录](novelty_repository_observation_2026-10-26.json)；其中 checked_at 与仓库自身的 updated_at 是不同字段。

当前 API 元数据为：创建时间2026-10-18T15:35:40Z，最近推送2026-10-26T07:25:17Z，更新2026-10-26T07:53:56Z。上述字段均不能单独证明首次转公开的时间。匿名公开事件接口限流、认证请求超时，未取得 PublicEvent，因此没有给出推测的公开时间。[仓库 API](https://api.github.com/repos/Einsamake/maj-random-if-equal-lean)。

本地最终源 SHA256、统一内核验收和提交记录能固定成果内容与内部时间链；私有提交、可修改的Git日期及机器审计都不能单独证明“全世界最先公开”。本项目的网页自命中一律排除，不能拿自己的 README 佐证新颖性。仓库旧 description 仍写未完成，也不作为当前数学状态的证据。

## 覆盖限制与可使用的表述

OpenAlex 和 Semantic Scholar API 本轮均限流，未取得完整前向引文清单；Google Scholar、Web of Science、Scopus 未取得完整导出。Consensus精确规则查询只返回原论文，宽化查询传输失败；它只是候选发现工具，不构成完整引用追踪。Crossref计数也不是引文清单。

原作者2023 HDR、2019会议前身及部分幻灯没有完整读取。公开 GitHub／数学预印本目录检索受索引和访问限制。尚可能遗漏其他术语、近期上线、付费数据库内、未索引或未公开的成果。全部成功和失败范围分别见[作者路线](novelty_authors_2026-10-26.md)、[后续引用路线](novelty_forward_2026-10-26.md)和[形式化路线](novelty_formal_2026-10-26.md)。

当前适合使用的表述是：

> 我们给出 Fatès–Marcovici–Taati Question7.4 所述同步模型的二次阶恢复时间证明，并完成其自含 Lean 形式化。截至2026-10-26的定向公开文献与代码检索，未发现同模型结论或同题完整形式化的先行公开证明。全球优先权尚待进一步核查。

如需把主张提升为正式的首次解决声明，还须核查遗漏的前向引文和原作者材料，固定可由第三方验证的首次公开版本，并请熟悉该领域的研究者指出可能先例。没有单一网站、搜索次数或人工评审能提供全球不存在其他证明的逻辑保证。本轮没有联系作者、提交文章、对外发布或更改正式数学源。
