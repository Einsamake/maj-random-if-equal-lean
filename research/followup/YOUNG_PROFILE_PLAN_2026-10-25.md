# 下一阶段接口：行长与有限排斥粒子编码（待证明）

2026-10-25，只读核查与证明规划；本页没有新增 Lean 源或启动构建。以下是候选接口，不能计入已形式化成果。令 M=n+2，f:Fin M×Fin M→Bool 且 Monotone f，0 为西南序理想。

## 索引与方向核查

定义 λ_y = #{x:Fin M | f(x,y)=false}。应证明 0≤λ_y≤M、λ 随 y 反单调，以及 f(x,y)=false ↔ x.val<λ_y。推荐直接用 Fin.rev：p_r=r.val+λ_(r.rev)，其中 r.rev.val=M−1−r.val。于是 p 严格递增、p_r<2M。全 true 初态 λ=0 对应粒子占0,…,M−1；全 false 对应 M,…,2M−1。

右半粒子数 J=#{r:Fin M | M≤p_r}。换元 y=r.rev 得 M≤p_r ↔ y.val+1≤λ_y，故 J 是白色对角格的数量。最干净的接口是 **f(d,d)=false ↔ d.val<J**（d:Fin M）。由此当 **1≤N≤M** 才能写 J≥N ↔ f(N−1,N−1)=false；N=0 时后一写法因 Nat 截断减法而不成立，必须排除。

单个实际更新：把一个1格变成0格时，所在行 λ 增1，对应 r=y.rev 的粒子向右移1；0变1则向左移1。方向与空理想初态左半占据一致。不是把所有格子单向永久删除；两种 tie 翻转均保留。bottom行对应最后粒子，top行对应首粒子。

## 建议模块与最短接口

1. **YoungRows**：rowZeros f y 为 univ.filter；rowLength 为其 card。证明 rowLength_le_side、rowLength_antitone、false_iff_lt_rowLength、rowLength_update_other，以及实际新增/删去白格使本行 card±1。
2. **YoungParticles**：particle f r : Fin(2*M)，val=r.val+rowLength f r.rev；证明 particle_strictMono、particle_injective、particles_card=M、particle_initial。定义 rightCount 先直接数粒子标签 r，随后证明等于实际右半槽占据数；用 Fin.rev 的双射证明 rightCount_eq_diagonalZeros，再由对角 Bool 函数单调性给 diagonal_zero_iff_lt_rightCount。
3. **双向编码**：先以严格递增 M元位置列为中间结构。其范围必满足 r.val≤p_r≤r.val+M（后一式用右侧尚余粒子数量）；逆定义 λ_y=p_(y.rev)−y.rev.val，及 f(x,y)=decide(λ_y≤x.val)。证明 λ反单调、f单调和两向复合恒等。若需要从槽占据集合直接取逆，使用 Finset.orderEmbOfFin，避免手写排序。
4. **真实交换桥**：引用 MixedSquareCorners 的实际翻转分类；白格新增时 x=λ_y，且下一粒子至少位于 p_r+2（south输入为0），所以右侧目标空。删白格时 x+1=λ_y，前粒子≤p_r−2（north输入为1），所以左侧目标空。边界无相邻粒子时分别用 p_r<2M−1 或0<p_r处理。证明其他所有粒子不动，再得相邻占据01↔10交换。每格rate1、fair tie只给rate1/2；这一速率仍须真正generator证明。

## 已在当前 mathlib 源码核对的 API

- `Fin.card_Iio`：`(Finset.Iio b).card=b.val`；`Fin.card_Iic`：card=b.val+1，文件 Mathlib/Order/Interval/Finset/Fin.lean。建议据此证初段性质：若 f(x,y)=0，Iic x⊆rowZeros，故x+1≤λ；若为1，则rowZeros⊆Iio x，故λ≤x。这样自动处理 λ=M，无需构造 Fin M 的端点 M。
- `Finset.card_le_card`、`Finset.card_filter_le`、`Finset.eq_of_subset_of_card_le`、`Finset.card_bij`/`card_bij'`，文件 Mathlib/Data/Finset/Card.lean；结合 filter 集合外延、card_insert_of_notMem/card_erase_of_mem 做单格行长更新。
- `Fin.rev`、`Fin.val_rev`、`Fin.rev_rev`、`Fin.rev_injective`、`Fin.rev_le_rev`/`rev_lt_rev`、`Fin.revPerm`，文件 Mathlib/Data/Fin/Rev.lean及Finset/Fin.lean。标签换元优先用现有逆序双射，避免裸 Nat 减法反复变形。
- `Finset.orderIsoOfFin`、`orderEmbOfFin`、`orderEmbOfFin_mem`、`image_orderEmbOfFin_univ`、`orderEmbOfFin_unique`，文件 Mathlib/Data/Finset/Sort.lean；这些给实际有限粒子集合的递增枚举，不需递归整条H/V路径。

本阶段只推进有限几何/编码与实际更新关系。没有证明 SSEP 时刻law、矩方程、Poincare、协方差界、CLOCK上界或最终主定理；这些必须分别从真实过程推导。
