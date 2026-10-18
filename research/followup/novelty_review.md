# 两个候选结果的一手文献与新颖性边界审查

日期：2026-10-13。范围：独立核对已公开的一手来源与候选结果的关系；不替代证明审查、专家审阅或优先权认证。没有联系作者。本报告不修改总报告。

## 1. 当前可以支持的结论

- **同步多数规则**：直接核对的 2022 原文把目标规则的最坏期望恢复时间上界列为立方，并在 Question 7.4 猜测二次；2025 作者综述仍介绍立方上界。本轮没有找到把该规则明确证明为 Θ(n²) 的后续一手结果。候选结论与已核对的公开基线不同，但尚不能据此确认首次解决。
- **辅助调度技术已有明确先行文献**：Poisson 因果链的 O(t+log N) 深度及其具体尾界，在 Liu–Yin 的单格动力学并行模拟论文中已有；局部等待、max-plus 路径与有界度恒定模拟速度，也有 Lubachevsky 1987、Rajsbaum–Sidi 1994 的经典前身。应引用这些工具，避免把它们本身当作新发现。
- **二维向量回归**：2026-10-02 的 arXiv:2608.30254v2 仍明确列出三点猜想 13/8，通用已证上界 15/8。候选 11/6 比这个已核对基线强，但没有达到猜想。没有检出同一 11/6 一手结果；其新颖性仍待更全面核查。

下文 N 一律指有限区域的格子数；n 指初始扰动的包围方形边长。不能混用这两个参数。

## 2. 同步二维多数问题：原问题与已知连续时间定理

### 2.1 Fatès–Marcovici–Taati 2022

一手原版：[作者 PDF](https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf)，[arXiv v3](https://arxiv.org/abs/2101.12682v3)。期刊页码如下：

| 位置 | 核对内容 | 与候选结果的关系 |
|---|---|---|
| p.31，§1.2 | 有限集合直径是能装入的最小格点方形边长 | n 不是错误格数 |
| p.54，§4.1–4.2 | 速度是确定初态的最坏期望恢复时间；四相邻格多数，平局独立公平取样 | 虽把中心格列入邻域记号，规则实际不读取中心旧值 |
| pp.54–56，Proposition 4.1 | 最坏期望恢复时间至多立方；按行消去得到此界 | 正是候选二次上界的公开基线 |
| pp.55–56，证明 | 一维边缘过程已使用偶/奇时空位置拆分 | parity 拆分的思想本身不是全新；二维 heat-bath 迁移需另外论证 |
| p.79，Question 7.4 | 询问精确恢复速度并猜测二次 | 匹配下界也是回答“精确速度”的一部分 |

该来源还在 Example 4.2 指向异步 Poisson 版本。**连续时间结论不能直接冒充同步结论**；它们的更新核次序不同。

### 2.2 Marcovici 2025 作者综述

[Cellular automata and self-organisation phenomena](https://marcovici.perso.math.cnrs.fr/Publications/Marcovici_ESAIM2025.pdf)，ESAIM: Proceedings and Surveys 80:17–25。

§3.2，期刊 p.24（PDF 第 8 页），描述四相邻格多数加均匀随机平局，并仍介绍至多立方的恢复界。这是 2025 的作者报告基线，不是对 2026-10 的绝对开放性证明。

### 2.3 Caputo–Martinelli–Simenhaus–Toninelli 2010/2011

[原作者稿 arXiv:1007.3599](https://arxiv.org/pdf/1007.3599)，题名 *“Zero” temperature stochastic 3D Ising model and dimer covering fluctuations: a first step towards interface mean curvature motion*。

- 模型设置：§2，独立 rate-1 Poisson 时钟与单格 heat-bath；零温平局以概率 1/2 取两种自旋。
- **§3.2，Theorem 2，式 (3.4)，印刷 p.7**：二维方形 Λ_L={−L,…,L}²、固定全加边界、内部初态全减，τ₊ 为全加首次到达时间；存在 c,γ>0，对每个 L≥1，P(cL²≤τ₊≤c⁻¹L²)≥1−e^(−γL)。证明下界在 §8，pp.31–36。
- 全部自旋反号后，恰为候选证明需要的全零边界、实心全一方岛连续时间模型；边长 2L+1 与 n 只差常数。
- **Remark 2** 明确区分其匹配下界与此前 FSS 的带对数损失下界。不得把这个二维定理误读成标题中的三维结论。
- **Theorem 3 后的说明**指出 β=∞ 时平衡测度集中于一个配置，通常的平衡谱隙无非零方差可测函数。因此有限温度谱隙比较并不会自动比较零温最坏吸收时间。

## 3. 调度/扫描比较：最接近的已有结果

### 3.1 Peres–Winkler：censoring 是已知工具，已有扫描界有损失

[Can extra updates delay mixing?，arXiv:1112.0603](https://arxiv.org/pdf/1112.0603)（预印本页码）：

| 定理与位置 | 精确范围 | 不能直接替代的部分 |
|---|---|---|
| Theorem 1.1，p.4 | 有限单调系统，平衡测度在状态空间为正，从最大配置出发；删去有限单格 heat-bath 更新子序列后，删后分布随机支配完整分布；允许按预先规定分布随机选序列与子序列 | 候选必须先到有限温度，再对固定有限更新序列取 β→∞；删除机制不能窥视自旋随机标记 |
| Theorem 3.1，p.11 | 二部单调系统：任意 systematic scan 从最大态的混合时间≤2倍 alternating scan | 同步相邻格更新不是这一 sequential scan |
| Theorem 3.2，p.11 | random scan 从最大态混合时间≤2log N倍 alternating scan | 用全颜色 coupon 等待，每层付 log N；不能给匹配二次下界 |
| Theorem 3.3，p.11 | systematic scan≤O(√(ΔN))倍 random scan | 不能给候选所需的常数或加 log N 时间比较 |

候选的双向嵌入比该文现成的扫描比较更细；应表述为应用已知 censoring 后另行证明的局部调度比较，而非引用 Theorem 3.2/3.3 就已完成。

### 3.2 Liu–Yin：候选因果深度界几乎原样已有

一手来源：[arXiv:2111.04044v2 PDF](https://arxiv.org/pdf/2111.04044v2)，[HTML](https://arxiv.org/html/2111.04044v2)。作者 Hongyang Liu、Yitong Yin。v1（2021）题名 *Simple Parallel Algorithms for Single-Site Dynamics*，对应 STOC 2022；v2（2024-12-20）题名 *Parallelize Single-Site Dynamics up to Dobrushin Criterion*。

- **式 (5)–(6)，pp.10–11**：更新的 inclusive-neighborhood predecessor 形成 dependency DAG，包含同格前驱。
- **Lemma 3.11，pp.13–14，§3.2**：N 个独立 rate-1 Poisson 时钟、最大度 Δ，任一更新深度≥ℓ 的概率≤N[e(Δ+1)t/ℓ]^ℓ；随即得深度 O(Δt+log(N/ε))。它追溯 FHY2021 与 Hayes–Sinclair2007。
- **Theorem 5.1，p.22（PDF 第 23 页）**：任意初态、有限局部状态空间，给局部概率计算 oracle；0<t≤N^c₀，在 influence matrix 某 ℓ_p 范数≤ρ 条件下，以高概率 O(ρ(t+log N)) 并行深度忠实模拟。
- 候选格点规则 Δ≤4，局部核每邻居影响≤1/2，故 ℓ∞ influence 范数≤2（边界只减少项）。满足常数 ρ，无需高温快混合；但应使用**时钟依赖**的 Lemma 3.11，而不是选择依赖随机自旋消歧结果的快速子图来做 censoring。

**对照**：候选引理 E 的 N(5et/k)^k 就是 Δ=4 的同一已知估计。候选 rank 保留所有同格/邻格非交换更新的次序，比该文只列最近前驱的 dependency DAG 在应用目的上更保守；其链长度估计已有。把事件嵌为全颜色扫掠子序列、再用于 extinction stochastic domination，并不由其“忠实并行模拟”定理自动给出，仍需候选中的 trace/commutation 论证。

### 3.3 Hayes–Sinclair 2007 与 FHY2021

[Hayes–Sinclair 原作者稿](https://arxiv.org/pdf/math/0507517)，*A general lower bound for mixing of single-site dynamics on graphs*，Annals of Applied Probability 17(3):931–952。

§3.1，**Observation 3.2，预印本 p.11** 给沿有序 Poisson 事件路径的 (et/r)^r 界；Lemma 3.1 用路径计数控制有限传播。正式 statement 写独立时钟；候选允许路径重访同格时，仍应保留自己的 factorial-moment 或强 Markov 推导，而不省略这项核查。

[Feng–Hayes–Yin 原稿](https://arxiv.org/html/1904.00943)，*Distributed Metropolis Sampler with Optimal Parallelism*，SODA 2021。§6 的 dependency-chain 分析与局部保序并行化也是直接前身；其更快求值使用 Metropolis filters 的 Lipschitz 条件，不应自动等同于候选 heat-bath censoring。

### 3.4 Lubachevsky 1987：局部时间等待保真模拟已有

[Efficient Parallel Simulations of Asynchronous Cellular Arrays，作者修正版](https://arxiv.org/html/cs/0502039)，原发表于 Complex Systems 1 (1987)。

§2 明确纳入 Poisson asynchronous cellular arrays 与连续时间 Glauber；**§3，Figures 3.1–3.6** 给局部时间极小值/局部等待的保守模拟方案，依相邻 PE 时间推进并保持原更新历史。§4 的速度主要为实验。该文足以否定“局部等待准确模拟 asynchronous CA 是新技术”的宽泛声称，但本轮未在该文检出适用于候选固定 r 层任务的统一 O(r+log N) 有限尾定理。

### 3.5 Rajsbaum–Sidi 1994：逆向 readiness 的 max-plus 机制已有

[作者机构保存的 PDF](https://groups.csail.mit.edu/tds/papers/Rajsbaum/RajsbaumSidi94.pdf)，*On the Performance of Synchronized Programs in Distributed Networks with Random Processing Times and Transmission Delays*，IEEE TPDS 5(9):939–950，doi:10.1109/71.308532。

- **§II，式 (1)，Theorem 2.1，pp.940–941**：完成时刻是上一层邻居完成最大值加本地处理时间，并等于路径处理时间和的最大值。
- **§IV，Lemma 4.2，p.945**：独立同分布 Exp(λ) 处理时间，固定节点的期望第 k 层完成时间≤最大唤醒时间+(4/λ)(1+k log Δ_in)；其证明用路径计数与指数尾。
- **Theorem 4.3，同页**：长时间单节点执行速率有只依赖节点度的常数下界；bounded degree 不随 N 衰退。

**对照**：候选 §13 的 readiness 递推、路径指数矩及 bounded-degree 线性层数消耗，属于这一经典机制。原文假设各任务处理时间全局独立；候选直接从共享 Poisson 时钟选事件，只证明每条固定路径的条件指数矩。要将其用于 clock-only censoring、保证不重复 ring 且同格/邻格 trace 保序，仍需候选的专门证明。原定理不直接声称这里的同步多数 extinction 下界。

### 3.6 其他扫描比较：相关但假设或损失不覆盖目标

| 一手来源 | 精确结果与假设 | 此模型的适用边界 |
|---|---|---|
| [Guo–Kara–Zhang，Layerwise Systematic Scan，AISTATS2018](https://proceedings.mlr.press/v84/guo18a/guo18a.pdf)，Theorem 1 / Corollary 5，PDF 第5页 | 二部条件独立分布、random-update Gibbs ergodic；alternating 的**整轮** relaxation time≤random 的**单次格更新** relaxation time；TV比较另有 log(4e²/π_min) | 有一个 N 的时间尺度差异；不可把谱隙比较当 O(t+log N) 零温吸收比较 |
| [Blanca–Zhang，APPROX/RANDOM2023](https://drops.dagstuhl.de/storage/00lipics/lipics-vol275-approx-random2023/LIPIcs.APPROX-RANDOM.2023.53/LIPIcs.APPROX-RANDOM.2023.53.pdf)，Theorem 6，53:4；[Algorithmica2025 Theorem1.6](https://doi.org/10.1007/s00453-025-01353-5) | totally-connected 单调系统，η-spectral independence、固定 b>0 marginal bound；**对称化**的正序+逆序 scan 为 O(log N) | β→∞ 时全状态局部正边缘下界不能保持固定 b；平衡集中一点，也不能覆盖从平衡支持外的实心方岛吸收 |
| [Gaitonde–Mossel，SODA2026 / arXiv:2410.11136](https://arxiv.org/html/2410.11136)，Theorems1.1–1.4 | 一般 Gibbs sampler，scan整轮与random格更新的混合/谱隙有多项式比较 | 不给局部有界度 monotone 的无面积损失吸收时间迁移 |
| [Kwon，Cost Comparisons…，arXiv:2610.01121v1](https://arxiv.org/pdf/2610.01121v1)，2026-10-01，Theorems1.1–1.2，pp.3–4 | reversible block updates、global block-wise contraction；按 reciprocal norm-gap 计更新成本；random最多常数倍，反向可差 O(d²) | 最新相关 2026 预印本，研究平衡 L² norm-gap；非 candidate 的固定时间 clock-only stochastic domination |

## 4. 回归三点问题：已核对公开边界

### 4.1 主来源与确切版本

[Zhang，arXiv:2608.30254v2 PDF](https://arxiv.org/pdf/2608.30254v2)，[HTML](https://arxiv.org/html/2608.30254v2)，最新版记录为 2026-10-02。

| 位置 | 已知结果 |
|---|---|
| p.10，Theorem 6.4；pp.26–27，Lemma E.4 / Appendix E.5 | F_weighted(2,2,3)∈[13/8,15/8]；star localization 只给通用额外损失7E/8 |
| p.10，Conjecture 6.5；p.27重述 | 精确值猜想13/8，等价三点额外损失≤5E/8 |
| p.25，Lemma E.1 | 三点内重加权的 inf 等于有效 B_ij 凸包到0的距离平方；部分边界只在权重极限达到 |
| p.11，Proposition 6.6；pp.28–32，Appendix F | 至多七原子规约；两方向和至多四原子的三点子类已解决 |
| p.12，Discussion / Reproducibility | 作者仍明确把 Conjecture 6.5 列为开放 |

候选证明的 5E/6→11/6 不在核对的 v2 结果中。它用 star 的完整二维协方差代替只用 trace 的 E/4 均值近似；这是一个可以精确与已有 Lemma E.4 对照的局部改进。仅有内部证明和未检出的相同常数，尚不能宣称原创。

### 4.2 邻近新稿不能当作同一解

[Liu–Wang，Weighted Data Selection: Sharp Upper-Half and Five-Dimensional Laws，arXiv:2610.00101](https://arxiv.org/html/2610.00101)，§1–4 / Theorems1–2，研究标量输出的 Γ_d(n)，特别是 (d,n)=(5,6) 的 11/5；其参考文献引用 Zhang 的**标量**稿 arXiv:2608.28007。模型、维数、预算及常数都不同，未给本二维向量三点 13/8 或 11/6。

### 4.3 协方差两点引理的边界

候选新用的引理是：有限零均值 R² 点系协方差 Σ，总能从原点系中选至多两个点作凸组合 δ，满足 ||δ||²≤detΣ/trΣ（奇异情况为0）。这比仅用 traceΣ/4 的各向同性上界更细。

该引理的 polytope/circuit 分解、三角形重心几何，以及矩阵调和平均的凹性是标准工具；不能因文稿提供了自含推导就称引理首次提出。原论文 Appendix G 的 Theorem G.1 / Lemma G.2 提供 variance-normalized 的 simplex skeleton 稀疏化，与这里的 covariance-sensitive 界相关，但不是相同陈述。该附录也明确区分等权 pair、半径归一化与任意凸权重。

另行直接核对的 [Tinarrage，Sharp approximate Carathéodory theorem…，arXiv:2606.25854](https://arxiv.org/html/2606.25854)，§4.1 Theorem3，归一化条件是所有顶点在单位球内，选择是允许重复的 k-元**等权**重心；没有给这里的协方差逆迹归一化陈述，因此不能把它当作候选协方差引理的直接来源。

本轮没有找到包含同一 detΣ/trΣ 两点结论或其 11/6 应用的明确一手来源；这里的**未找到**只表示检索边界，不表示引理或应用此前不存在。

## 5. 检索覆盖、排除方式与建议措辞

检索既使用题名/arXiv号/作者/精确常数，也扩展到：Maj-Random-If-Equal、PCA erosion、zero-temperature synchronous/parallel heat-bath、alternating/red-black scan、censoring、bounded-degree systematic/random scan、parallel discrete-event simulation、dependency DAG、Poisson causal path、stochastic synchronizer、max-plus processing-time recursion、weighted vector-valued regression selection、variance/covariance-sensitive approximate Carathéodory。

原版/作者 PDF、arXiv 全文与版本记录、正式会议/期刊网页用于结论。聚合站和二手搜索片段仅用于发现候选链接，不作为数学主张依据。Rajsbaum–Sidi PDF可被检索器读到，但截图和本地下载失败；这里没有以不可读数式做新推论，只引用可复核的递推、Lemma4.2和其度依赖结论。仍可能遗漏以其他术语发表、未充分索引、刚上线或未公开的成果。

对外建议写：

> 我们给出一份回答 Fatès–Marcovici–Taati Question 7.4 的候选二次阶证明。证明结合已知的零温连续时间方岛消失估计、Peres–Winkler censoring、已有 Poisson 依赖路径界与局部同步器思想；专门论证双向颜色扫描嵌入。内部独立审查暂未发现缺口，一手文献审查未检出同一结论，外部验证与优先权核查尚未完成。

> 对二维向量回归的三点问题，我们获得一份把已核对上界15/8改进为11/6的候选证明，原13/8猜想仍未解决。新增步骤是对star协方差的细化和平均估计；不作此前未知的保证。

若要正式提交，应首先把辅助引理来源补齐，再由概率/CA专家核查固定温度极限、clock-only deletion与全部非交换更新保序；回归稿应明确承认原论文的closure identity、star localization、已解子类与七原子规约。
