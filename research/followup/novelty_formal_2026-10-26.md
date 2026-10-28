# 同题形式化先例与方法先例核查（2026-10-26）

结论：本轮没有找到独立于本项目、公开可核对的「无限二维同步四邻 Maj-Random-If-Equal 最坏恢复期望 Θ(N²)」完整 Lean、Isabelle 或 Coq 证明。这是限定范围内的检索结果，不能认证全球首个形式化，也不能认证数学结论首证。特别是，公开 GitHub 代码检索连本项目的新代码也尚未命中，说明索引存在时滞。

本报告只做先例检索；没有重新验证本项目的 Lean 证明，没有修改正式源码，也没有联系作者、修改仓库可见性或发布内容。

## 什么才算同一先例

需同时吻合：无限 Z²；四个轴向邻居且不计中心；每轮所有格点同步更新；平局独立公平；初态是齐次背景的有限扰动；N 是最小平移半开轴向方形的边长；时间是同步轮数；结论是最坏初态的扩展期望两侧二次界。连续时间、有限周期网格、高温平稳混合、均场 ODE、有限模拟、条件性形式化均需另行对照，不能直接算同一结论。

## 已发现而应排除的宽泛“首创”说法

| 公开原始来源 | 已核对内容 | 对本项目的含义 |
|---|---|---|
| František Silváši、Martin Tomášek，2020，*Lean formalization of bounded grids and computable cellular automata defined thereover*，Science of Computer Programming 195:102471，https://doi.org/10.1016/j.scico.2020.102471 | 出版方摘要：有界网格、矩阵解释、可计算 CA 框架和性质。 | 不能称首个 Lean 元胞自动机形式化。没有在此来源找到本题随机恢复 Θ(N²)。 |
| 同作者，2020，*Extending Lean Cellular Automata Framework – Boundary Conditions and Properties of Canonical Forms*，Acta Electrotechnica et Informatica 20(1):32–38，https://aei.tuke.sk/papers/2020/1/5_Silvasi.pdf ，DOI10.15546/aeei-2020-0005 | 直接读取7页原文：固定/周期边界、canonical form、非空状态计数性质；公开实现 https://github.com/frankSil/CAExtensions ，leanpkg.toml 固定 nightly-2019-01-13。 | 元胞自动机和边界处理的形式化已有先例；本题的概率首达和二次尺度没有出现在所读内容中。 |
| Kuldeep S. Meel，公开源码 https://github.com/meelgroup/arlib/blob/8d08f89a6d05c5e8368e91659bd6e117fbb74c4e/Arlib/MarkovChains/Chains/Glauber.lean | 通过 GitHub raw API 直接读取前95行：有限 V 上随机选单点热浴，详细平衡、平稳性、半正定。 | Glauber/热浴形式化本身已有公开代码。不同于无限同步二维有限缺陷的恢复尺度。没有对该仓库做完整独立构建审计。 |
| 公开源码 https://github.com/hxrts/stat-mech/blob/ab32b969285e24f8b054f7f008e1f8e798abd375/StatMech/MeanField/Examples/Ising/Glauber.lean | 通过 GitHub raw API 直接读取前95行：均场 Ising 的局部翻转速率和宏观 drift 代数。 | 不能把“首次形式化 Glauber”当贡献；所读源码没有二维空间几何与最坏首达期望。 |
| Emin Karayel，*Negatively Associated Random Variables*，AFP，2025-01-16，https://isa-afp.org/entries/Negative_Association.html | 直接读取官方条目：负关联定义、闭包、Chernoff–Hoeffding、FKG、置换/Bloom filter 示例。 | 一般负关联的机器形式化已有先例；此条目没有陈述本题或 SSEP 消滴定理。 |
| Johannes Hölzl、Tobias Nipkow，*Markov Models*，AFP，2012-01-03，https://isa-afp.org/entries/Markov_Models.html | 直接读取官方摘要/会话列表：Markov 模型、奖励、pCTL 和协议应用。 | 概率过程和首达分析基础并非本项目独创，不等于本题已有完整形式化。 |

还直接读取 AFP 官方总目录 https://isa-afp.org/ 和含33项的 Probability theory 目录 https://isa-afp.org/topics/mathematics/probability-theory/ 。总目录对 Cellular、Majority、Exclusion、Ising 的文本查找无匹配；概率目录未见同题标题。这只覆盖条目标题和说明，不是所有 Isabelle 源码的穷尽语义检索。

## 实际公开检索记录

检索时间为2026-10-26。使用网络搜索及 GitHub 只读 REST API。原始成功/失败与命中链接保存为同目录的 novelty_formal_github_search_2026-10-26.json；补检保存为 novelty_formal_github_search_supplement_2026-10-26.json。

已实际成功的精确 GitHub code 查询（均返回 incomplete_results=false）：

- Maj-Random-If-Equal：total_count=0。
- MajRandomIfEqual：0。
- 2101.12682 extension:lean：0。
- SimpleExclusion extension:lean：0。

相邻宽泛查询 Glauber extension:lean 返回812条，Glauber zero temperature extension:lean 返回26条，symmetric exclusion extension:lean 返回2040条；它们含群论 Glauberman、普通“对称/排除”等大量歧义。本次只读取限定返回页和代表性源码，不把这几组当穷尽筛查。具体条数只描述当时 GitHub 搜索索引，不是全世界的作品数。

网页检索实际包含这些查询组：

- “Maj-Random-If-Equal” + Lean / formal proof / formalized / Isabelle / Coq / Agda；
- “2101.12682” + Lean；
- “Self-stabilisation of cellular automata on tilings” + formalization；
- “cellular automata” + Lean / Isabelle；
- “Glauber dynamics” + Isabelle；
- “symmetric exclusion” + Lean / Coq；
- GitHub、AFP 域名限制下的相应检索。

检索命中的原论文元数据、arXiv 镜像、书目清单和本项目自己的仓库均不当作独立证明。GitHub 精确名称 repo 查询只返回本项目，所以必须排除自命中。网络中出现 EOF/TLS timeout 的 API 请求在记录中标记失败，没有把失败当零结果。

现场附注：GitHub repo search 对本项目返回 isPrivate=false（createdAt2026-10-18T15:35:40Z，updatedAt2026-10-26T07:53:56Z），与旧 private=true 验收快照不同；我没有更改该状态。仓库创建时间和最新更新时间本身都不能证明完整主定理何时首次公开，公开优先权须另核具体提交与当时可见性。

## 方法层面的先例边界

Caputo–Martinelli–Simenhaus–Toninelli 的公开原文 arXiv:1007.3599v2（2010-09-14；期刊2011）https://arxiv.org/pdf/1007.3599 明确处理连续时间单点 rate1 的 Glauber/零温消滴，二维 L² 上界归于 Fontes–Schonmann–Sidoravicius，提供对应二维下界；一般单调全局耦合也在其正文列明。Liggett 的 *Negative Correlations and Particle Systems*（2002, MPRF8(4):547–564）https://math-mprf.org/journal/articles/id948/ 已研究对称排斥的负依赖。

因此，SSEP、负相关、热方程/Poincaré、单调耦合不能整体声称由本项目新发明。可能需要进一步判断的贡献，是这些工具在本题精确同步模型中的组合、连续/同步和跨尺寸桥接、以及完整无核心前提的 Lean 实现。前两者仍需逐定理对照前人文献；最后一项目前可表述为“本次检索尚未发现同题公开完整形式化先例”。本项目最终证明自行建立所需弱清空界，不能把其说成直接调用了 CMST/FSS 完整结论。

## 可支持的措辞

“截至2026-10-26，在本报告列明的公开文献、代码索引和形式化档案范围内，未发现独立的同题完整机器证明。我们已完成该精确模型的 Lean 形式化；关于数学首证和形式化优先权，仍需结合完整文献对照、公开版本日期及领域专家意见确认。”

不能由本次工作推出“全球首次已被认证”“原问题截至今日必定仍开放”“所有核心数学方法均原创”。未发表、未索引、非英文、不同术语和尚未公开的工作仍可能存在。

## 补检的实际结果

novelty_formal_github_search_supplement_2026-10-26.json 记录：Marcovici extension:lean 和 MajRandom extension:v 成功返回0；MajRandom extension:thy、SSEP extension:lean、majority eroder extension:lean 重试仍EOF。synchronous majority extension:lean 返回81条，实际只检查其前10条和以下两个最相关文件：

1. https://github.com/formal-dynamics/leanamics/blob/ef4b8d60657213d8345512dc46dd461e505398c6/undecided/Undecided/Majority.lean ：直接读取完整文件；有限complete graph、节点每轮随机抽一个节点、三态undecided共识，结论O(log n)且w.h.p.。其引用为SODA2015/MFCS2018。该模型不是本题四邻格点随机平局规则。
2. https://github.com/vasnesterov/formal_podc/blob/78372b9fd498336f656e8e3410d14512f113f8a8/Papers/PODC2015/SynchronousCounting/Majority.lean ：直接读取完整文件；有限列表多数值选择器和超过半数/少数坏节点的确定性性质，没有本题随机空间过程或二次期望结论。

这些代码已直接读取但未独立编译；只能说明所读声明的范围，不为其内核正确性背书。
