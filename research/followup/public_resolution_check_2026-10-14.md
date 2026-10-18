# Question 7.4 的公开解答定向核验

核验日期：2026-10-14，北京时间约 01:34–01:43。执行代理：/root/public_resolution_check。范围：公开文献、作者页面、预印本版本和正式发表记录；未联系作者、未对外发布。先读取本地 ca_clean_proof.md、novelty_review.md 和已有模型审查，再实际联网复核；下述状态判断以本次读取的一手来源为依据。

## 当前判断

**本次未检出同一二维同步模型的公开 Θ(n²) 最坏期望恢复时间定理。** 这不是“问题截至今日仍开放”的证明，也不是本地候选证明的新颖性、正确性或优先权认证。原论文当前 arXiv 页面仍将 v3（2022-03-05）列为最新版本；其 Question 7.4 保留二次猜想。2025 年作者综述继续介绍立方界。新检出的近邻结果，经核对有模型或目标差异，不能视为该问题的解答。[原论文版本记录](https://arxiv.org/abs/2101.12682)、[2025 作者综述](https://marcovici.perso.math.cnrs.fr/Publications/Marcovici_ESAIM2025.pdf)

本地候选 Θ(n²) 论证与已经核对的公开立方基线不同；是否此前已有等价证明仍待更完整的引文追踪及领域审阅。此次检索没有发现与本地候选规则直接矛盾的同模型定理。

## 1. 原问题核验与定位

来源：Fatès–Marcovici–Taati，Self-stabilisation of Cellular Automata on Tilings，Fundamenta Informaticae 185(1):27–82 (2022)。[作者 PDF](https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf)、[arXiv HTML](https://arxiv.org/html/2101.12682v3)。本次读取了相关 PDF 文字与 HTML。

| 原文位置 | 实际核对的内容 |
|---|---|
| §1.2，期刊 p.31，PDF 第 5 页 | n 是包含有限扰动的最小轴平行方形边长，非错误格数 |
| §4.1，期刊 p.54，PDF 第 28 页 | 同步独立更新；τ(n) 是确定初态的最大期望首次恢复时间 |
| §4.2，式 (36)，同页 | 只读四邻格；严格多数确定输出，平局独立公平重采样；中心虽列入邻域记号，但公式不读取中心值 |
| Proposition 4.1，pp.54–56 | 证明至多立方时间 |
| Question 7.4，期刊 p.79，PDF 第 53 页 | 问精确恢复速度并猜测二次 |

判定候选公开解答时，要求同时匹配这些模型条件及最坏期望时间目标；实心方岛的下界和任意有限扰动的上界分别核验。无限全零背景与有限方形固定零外部的等价属于本地证明的封闭性步骤，不能以环面结果代替。

版本记录：v1 2021-01-29；v2 2021-11-11；v3 2022-03-05。[arXiv](https://arxiv.org/abs/2101.12682)。正式记录存在日期差异：[Episciences](https://fi.episciences.org/9184) 标 2022-03-10，[SAGE 期刊页](https://journals.sagepub.com/doi/10.3233/FI-222103) 标首次线上发表 2022-03-18；不把两者合并成一个日期。二者对应同一期刊文章，而非检出的新解答。

编号提醒：作者期刊 PDF 将连续时间例编号为 Example 4.2，实验性 arXiv HTML 显示为 Example 4.3；Question 7.4 与 Proposition 4.1 均一致。需要精确引用时优先使用 PDF 页码、节和公式。

## 2. 后续作者资料与相关结果

| 来源、版本或日期 | 本次核验的具体位置及结论 | 与目标问题的关系 |
|---|---|---|
| [Marcovici，Cellular automata and self-organisation phenomena](https://marcovici.perso.math.cnrs.fr/Publications/Marcovici_ESAIM2025.pdf)，ESAIM: Proceedings and Surveys 80:17–25，首页标 February 2025 | §3.2，期刊 p.24，PDF 第 8 页：四相邻格多数、均匀随机平局，仍介绍至多立方的推广界 | 支持 2025 作者综述所述基线；不能单独证明 2026 的开放状态 |
| [Marcovici–Taati，Positive-rate PCA and IPS with stationary Bernoulli measures are rapidly forgetful](https://arxiv.org/html/2605.16904v1)，[版本页](https://arxiv.org/abs/2605.16904)，v1 2026-05-16；HTML 作者脚注另标 Last update: August 24, 2026 | Theorem 1 / Corollary 1：严格正局部转移、平稳 Bernoulli 测度下的指数遍历性及有限区域对数混合界 | 目标多数规则含确定输出、转移概率可为 0，故不满足严格正假设。不能以其快速混合替代吸收时间定理；两种日期照原来源分开记 |
| [Barbieri–García-Ramos–Taati，Cellular automata, percolation and dynamical dichotomies](https://arxiv.org/html/2410.23770v2)，[版本页](https://arxiv.org/abs/2410.23770)，v2 2024-11-13；作者检索索引列 2026 期刊记录 | Theorems 1.3–1.4：群上 Gilman 等度连续/敏感性二分的刻画；§2.2 的 CA 为确定性连续、平移等变映射 | 内容和目标都不同，不是随机平局有限岛恢复定理 |
| [Zehmakan，Majority opinion diffusion: when tie-breaking rule matters](https://link.springer.com/article/10.1007/s10458-024-09651-y)，2024-05-20，Autonomous Agents and Multi-Agent Systems 38:21 | §2.2，Theorem 2.5 和后续 Tightness：随机多数在一维环 C_n 的紧二次界；§1.1、Theorem 2.7 允许交替 blinking 终类；Theorem 2.1 一般图可指数慢 | 更新核的随机平局类似，但图、边界、终类和 n 的含义不同。环上二次界及一般图反例都不回答二维固定背景 Question 7.4 |
| [Nakar–Ron，Characterizing and Testing Configuration Stability in Two-Dimensional Threshold Cellular Automata](https://arxiv.org/html/2507.14569v1)，[版本页](https://arxiv.org/abs/2507.14569)，v1 2025-07-19 | §1：二维 m×n 环面，Thr_b 读取 Γ(ℓ)∪{ℓ} 的五格；Threshold-3 是确定性多数；结果为稳定结构与性质测试 | 含中心、无公平平局、目标不是有限岛期望消失。标题中的二维 majority 不能当作同模型解答 |
| [Caputo–Martinelli–Simenhaus–Toninelli，零温 Ising 论文](https://arxiv.org/html/1007.3599v2)，[版本页](https://arxiv.org/abs/1007.3599v2)，v2 2010-09-14；期刊 2011 | §2 式 (2.4)：独立 rate-1 单格 Poisson 更新；式 (2.17)：全负初态至全正；§3.2 Theorem 2 / 式 (3.4)：二维方形固定全正边界，P(cL²≤τ₊≤c⁻¹L²)≥1−e^(−γL) | 是本地候选采用的已知异步输入。自旋反号匹配岛/背景；更新方式仍须另证双向迁移，不能直接宣布同步解答 |

表中“不能替代”的判断是本次根据原文假设作的模型比较。没有把“检索片段里出现 quadratic”“题名有 majority”或“连续时间已有二次界”当作公开解决证据。

## 3. 作者页面、引文检索和访问边界

- 实际读取 [Irène Marcovici 主页](https://marcovici.perso.math.cnrs.fr/) 的发表列表。它列出 2025 综述、AUTOMATA 2025 渗流综述及 2026 正速率稿等；从该列表筛出的相关新稿已在上表核对。
- 实际读取 [Nazim Fatès 发表页](https://members.loria.fr/nazim.fates/publications.html)，并检索 [HAL CV](https://cv.hal.science/nazim-fates)。所读主页的 Recent 栏主要到 2024；不可据此假定该页覆盖所有 2025–2026 工作。
- [Siamak Taati 主页](https://siamak.isoperimetric.info/) 可被搜索引擎索引，列到 2026；直接打开多次返回 Internal Error。没有声称已完整读取该主页。索引提供的动态二分论文线索已转至原 arXiv 正文核验。
- 原文的 Google Scholar、NASA ADS、Semantic Scholar 跳转以及 Semantic Scholar/OpenAlex 引文 API 访问失败。因此本轮**没有获得并逐篇穷尽完整 cited-by 列表**。
- 额外使用学术索引作候选发现：精确规则名称搜索只返回原论文；宽化同步/随机多数/有限扰动/二次查询返回若干近邻论文。数学结论仍只依据上表所链接的一手正文。数据库的返回条数或未返回本身不构成开放性证据。
- 搜索发现 [Taati 2024 CIRM 报告页](https://www.carmin.tv/en/video/stabilising-shifts-of-finite-type-with-cellular-automata)（录制 2024-02-15，发布 2024-02-27）；仅查看可检索的页面资料，未观看视频。所链 slides 获取失败，不据此判断报告是否宣布问题解决。
- 作者 AUTOMATA 2025 渗流综述 PDF、2026 ALEA 相关幻灯片、Random Majority Percolation 作者 PDF 的完整打开失败；没有把检索片段作为相同模型的定理。原论文/2025 综述 PDF 的页截图也失败，本轮已核验的是可读 PDF 文字及 HTML，没有声称完成截图或整份文档视觉审查。

这些访问失败限制引文覆盖率，但不影响上表已实际读到的定理假设、版本记录和原问题定位。

## 4. 实际检索词记录

以下为本轮实际使用的代表性查询；精确查询、规则名称变体、作者/问题号、更新方式和近邻名词均有覆盖。查询中的排除域仅用于减少原论文镜像和聚合站，未把那些站点内容用作数学论据。

1. “Maj-Random-If-Equal” “time”
2. “Self-stabilisation of Cellular Automata on Tilings” citations
3. “Maj-Random-If-Equal” quadratic
4. “Maj-Random-If-Equal” stabilisation 2026
5. “2101.12682” “quadratic”
6. “Maj-Random-If-Equal” solved
7. “Question 7.4” “majority”
8. “Maj Random If Equal” quadratic
9. “Marcovici” “Taati” “quadratic”
10. “Maj-Random-If-Equal” “2026”；“Maj-Random-If-Equal” “2025”
11. Fates Marcovici Taati majority stabilisation quadratic 2023 2024 2025 2026
12. synchronous stochastic Ising droplet extinction quadratic time square lattice
13. random majority model square lattice finite islands extinction time
14. “synchronous” “zero-temperature” “droplet” quadratic majority
15. “random tie” “majority” “quadratic” cellular automata
16. “self-stabilisation” “majority” “quadratic”
17. “stabilization” “synchronous” “droplet” Ising
18. “Self-stabilisation of cellular automata on tilings” “cited by”
19. “FI-222103” 加原论文/期刊域排除
20. “random majority model” “torus” “stabilization”
21. “parallel zero temperature” “Ising” “droplet”
22. “parallel” “Ising” “droplet” “zero temperature”
23. “synchronous” “Ising” “extinction”
24. “probabilistic cellular automata” “finite” “eroder” majority
25. “random majority” “quadratic” “lattice”
26. “Self-stabilisation” “tilings” “2026” theorem
27. “Self-stabilisation of cellular automata” “2025” “majority”
28. “Maj-Random-If-Equal” “quadratic” proof
29. “Cellular automata, percolation and dynamical dichotomies”
30. 学术索引：精确规则名 + stabilization time；synchronous probabilistic cellular automata finite perturbations majority quadratic stabilization year:2022-2026

搜索结果中还出现含中心确定性多数、Toom 的不对称 NEC、带持续噪声的多数、环面共识、bootstrap percolation 等不同问题。没有把它们的线性、二次或指数时间措辞混进本地目标。

## 5. 主代理可以独立复核的最小集合

1. 原论文作者 PDF 的 p.54 式 (36) 与期望时间定义，p.79 Question 7.4；arXiv abs 页的 Submission history。
2. 2025 ESAIM 作者 PDF 的 p.24 §3.2；首页 February 2025。
3. 2026 Marcovici–Taati 稿 Theorem 1 的 strictly positive 假设；本地规则严格多数时的确定输出。
4. Zehmakan 2024 §2.2 / Theorem 2.5 的 C_n 及 §1.1 终类定义。
5. Nakar–Ron 2025 §1 的 Γ(ℓ)∪{ℓ} 和二维环面定义。

建议当前措辞：“原 2022 论文仍列二次猜想，2025 作者综述仍介绍立方界。本次定向文献核查未检出同一同步模型的公开匹配上下界；完整引文覆盖、外部证明审阅及优先权仍待核验。” 不据此使用“公认仍开放”“首次解决”或“已被证明成功”。
