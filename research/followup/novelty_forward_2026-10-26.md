# 前向引用与近邻模型独立检索

检索日：2026-10-26。目标：无限 Z²、同步四邻多数、平局在每格每轮独立公平掷币、原论文的确定初态尺寸 n 与最坏期望恢复时间 τ(n)=Θ(n²)。本文只记录公开先例查证，不认证全球不存在未索引或未公开证明。

## 结论

本轮已读的后续原始材料中，没有发现对目标命题的公开证明。可明确排除的近邻材料包括：2024 年零噪声不变测度稳定性论文、2023 年扰动铺砌博士论文，以及含正磁场/有限体积的同步 Ising 亚稳态文献。2026 年一维单调元胞自动机报告的会议页面、作者页面与检索到的定理摘录指向另一问题；其 PDF 本轮无法完整获取，因此不能记作全文核验通过。未检出并不构成“仍开放”或“全球首创”的证明。

## 可核原始来源

### 1. Marsan–Sablik，2024

Hugo Marsan, Mathieu Sablik, *Strong stochastic stability of cellular automata*, arXiv:2403.19932v1，2024-03-29。

- 原文：https://arxiv.org/html/2403.19932v1
- 已成功阅读全文结构、摘要、§1.3、§2 定义及参考文献。
- §1.3 的 FMT22 引用是说另一种稳定性用于纠正铺砌错误；本文主问题是微小持续噪声趋零时，扰动过程不变测度的极限，以及强随机稳定性的不可判定性。
- 原命题要求有限初态扰动、没有持续噪声、指定公平 tie 规则的同步恢复时间最坏期望。本文没有给出该 τ(n) 的二次上下界。
- 该结论基于原文定义与主定理范围，不能把“稳定性”同名当成同题。

### 2. Léopoldine Gayral，2023 博士论文

*Complexité et robustesse des pavages avec perturbations aléatoires*，Université Toulouse III Paul Sabatier，封面答辩日期 2023-06-23。

- 作者全文：https://lgayral.pages.math.cnrs.fr/files/manuscrit.pdf
- 148 页 PDF 本轮成功读取。检索 FMT22、majority、synchron，并检查所有返回的 FMT22 引用上下文和标题/研究设定。
- FMT22 的正文引用位于打印页 139（PDF 第 141 页），讨论由迭代元胞自动机作局部重构、denoising 和 global-agreement divergence；文献表位于打印页 141（PDF 第 143 页）。
- 论文主体是随机扰动铺砌、Besicovitch 稳定性、计算复杂性及低温 Gibbs 行为。p72 的 majority 构造在任意远窗口上选多数来恢复周期铺砌，平局按人为全序，既不是四邻局部同步规则，也不是目标恢复时间。
- 未发现本题 τ(n)=Θ(n²) 的证明。搜索引擎给此文件的“11 个月前/7 个月前”不能用作论文日期；以封面 2023-06-23 为准。

### 3. Poirier–Theyssier，2026 ALEA 报告：部分可读

Léo Poirier，joint work with Guillaume Theyssier，*Convergence for 1D monotonic cellular automata, starting from a random configuration*，Journées ALEA，CIRM，2026-03-09 至 13。

- 会议官网：https://conferences.cirm-math.fr/3551.html
- 日程：https://www.cirm-math.fr/Schedule/screen_display.php?id_renc=3551
- 作者研究页：https://leo-poirier.eu/recherche/
- Slides：https://www.cirm-math.fr/RepOrga/3551/Slides/Poirier_ALEA_2026.pdf
- 作者页面与会议节目均确认题目为一维单调 CA 的测度收敛。搜索索引可返回 slide17 的主定理：一维二元单调 CA 对满支撑、平移不变遍历初始测度的 Cesàro 平均收敛；以及 slide23 对 FMT22 的引用，涉及 stable eroder 对随机初态的 μ-nilpotence。
- Slides 中也有二维 majority 示例，不能仅因出现二维示例就判定同题。已读主定理摘录没有给有限扰动四邻随机 tie 同步规则的最坏恢复时间。
- 重要限制：PDF 多次 web open 超时；获准 PowerShell 直接读取仍 unexpected EOF。未成功阅读全文，不能在覆盖清单中写“全文已核验”。

### 4. 同步/异步 Ising 亚稳态近邻：不同参数极限

Emilio Nicola Maria Cirillo, Vanessa Jacquier, Cristian Spitoni, *Metastability of Synchronous and Asynchronous Dynamics*, Entropy 24(4),450，2022。

- 作者/出版全文：https://www.mdpi.com/1099-4300/24/4/450
- 存档全文：https://pmc.ncbi.nlm.nih.gov/articles/PMC9029560/
- 原文 §3.2–3.3 要求小正磁场 0<h≪1、有限晶格和低温极限；同步情形还假设偶数边长环面。结论是由亚稳态到稳定态的激活能/指数时间和 critical droplets。
- 目标命题是 h=0、精确零温公平 tie、不带周期边界的无限网格有限扰动，随 n→∞ 的 n² 恢复时间。上述文献不是目标证明。

### 5. 2019 前身会议文与其公开引用：全文覆盖有限

Fatès, Marcovici, Taati, *Cellular Automata for the Self-stabilisation of Colourings and Tilings*, RP2019，LNCS11674，121–136。

- DOI：https://doi.org/10.1007/978-3-030-30806-3_10
- HAL 标识：hal-02159155；作者出版列表：https://members.loria.fr/nazim.fates/publications.html
- 原作者列表确认该文是2019年前身。HAL 和 DOI 本轮全文获取失败，不能将元数据/摘要当作完整证明核验。
- 公开检索发现引用它的 Hongu–Hagiya *Self-Stabilizing Distributed Algorithms by Gellular Automata*（会议/扩展版本日期存在2020/2021/2022多条记录），研究迷宫、距离2着色及分布式 gellular automata 构造。HAL PDF：https://inria.hal.science/hal-03659466v1/preview/496967_1_En_7_Chapter_OnlinePDF.PDF 。本轮检索摘要与参考文献支持此不同问题分类；PDF直接打开失败。故不能当成已读全文或同题解决。

## 搜索覆盖和失败记录

查询包括：精确题名及 DOI/arXiv 编号；Maj-Random-If-Equal；majority/random tie/synchronous recovery/stabilisation；parallel/zero-temperature Glauber/droplet；synchronous Lifshitz law；2019前身题名的前向引用。结果多为原论文镜像、作者出版页、2025原作者综述以及上述近邻材料。

OpenAlex 公开 API 与 Semantic Scholar graph API 均尝试：web 工具无法访问；另以只读 PowerShell 请求，在正常权限下网络套接字受限，获准后两者均返回 HTTP429。没有获得完整 citing-works 列表，不能声明对这两个引用数据库的穷尽检索。Crossref 引用计数不等于完整清单。Google Scholar、Web of Science、Scopus 也未获得完整前向引文导出。

未联系作者，未对外发布，未改动数学源、既有审计或私有仓库可见性。本文件仅为主代理的独立检索输入，不单独给出全球优先权结论。
## 补查：Toom contours 的 2026 论文及 2025 companion

Jan M. Swart, Réka Szabó, Cristina Toninelli, *Peierls Bounds from Toom Contours*，Journal of Theoretical Probability，2026-05-11，DOI 10.1007/s10959-026-01508-2。

- 出版社原文：https://link.springer.com/article/10.1007/s10959-026-01508-2
- arXiv 前身：https://arxiv.org/abs/2202.10999
- 成功读取出版社 HTML 的模型、主定理、应用范围和相关讨论。
- §1.2 式(1.11) 所称 symmetric majority 是五输入（包含中心）确定多数；作者明确给出不能消失的 2×2 岛。它不是四邻公平随机平局。
- Theorem9 给共同严格正边缘速度条件下的小持续噪声稳定性；主结论22/25/26控制上不变轨迹的 Toom 轮廓概率。没有给目标 τ(n) 的二次恢复定理。

同作者 companion：*Peierls bounds from random Toom contours*，https://arxiv.org/html/2501.09660v1 ，arXiv 标识 2501.09660（头部 v1 标2025-01-16，正文标题页显示2026-08-24；本轮不自行解释此版本日期差异）。已读 §1.2–1.5：三项应用分别是 NEC Toom 规则的临界噪声下界、三角晶格上随机三输入含中心多数的稳定性、cooperative branching 与 identity 的混合规则。研究持续噪声下的上不变密度，不是本题的四邻随机 tie 恢复时间。