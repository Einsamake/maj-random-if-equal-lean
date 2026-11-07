# 有限有向网络的顺序保持原理

设 $V$ 为有限指标集，固定系数满足 $a_{ij}\ge0$、$d_i\ge0$。考虑

$$
x_i'=\sum_j a_{ij}(x_j-x_i)-d_ix_i+f_i(t).
$$

约定 $a_{ij}$ 表示坐标 $j$ 对坐标 $i$ 的作用系数。所有向量不等式均逐坐标理解。经典解在 $[0,\infty)$ 上连续，在每个正时刻可微并满足方程。

**命题。** 若 $x,y$ 分别为输入 $f,g$ 下的给定经典解，且 $x(0)\le y(0)$、$f(t)\le g(t)$，则对所有 $t\ge0$，有 $x(t)\le y(t)$。

当指标集为空时结论为空真；以下有限和论证同样适用。本命题不以网络平衡为条件，也不包含任意输入下解的存在性或时变流量系数的情形。

## 正部平方能量估计

令 $c=x-y$、$s=g-f\ge0$，则

$$
c_i'=\sum_j a_{ij}(c_j-c_i)-d_ic_i-s_i.
$$

定义 $\phi(r)=\max(r,0)^2$、$p_i=\max(c_i,0)$、$E=\sum_i\phi(c_i)$。$\phi$ 在零点也可微，导数为 $2\max(r,0)$；$E\ge0$，且 $E=0$ 等价于 $c\le0$。

所需标量不等式为

$$
2\max(\alpha,0)(\beta-\alpha)\le\phi(\beta)-\phi(\alpha).
$$

当 $\alpha,\beta\ge0$ 时，右边减左边为 $(\beta-\alpha)^2$；当 $\alpha\le0$ 时，左边为零、右边非负；当 $\alpha>0>\beta$ 时，差为 $\alpha^2-2\alpha\beta\ge0$。因此

$$
\begin{aligned}
E'
&=2\sum_{i,j}p_i a_{ij}(c_j-c_i)
  -2\sum_i d_ip_ic_i-2\sum_i p_is_i\\
&\le\sum_{i,j}a_{ij}[\phi(c_j)-\phi(c_i)]\\
&=\sum_i\left(\sum_j a_{ji}-\sum_j a_{ij}\right)\phi(c_i).
\end{aligned}
$$

在 $c_i>0$ 时 $p_i=c_i$，在 $c_i\le0$ 时 $p_i=0$，所以 $p_ic_i=p_i^2\ge0$；泄漏项与输入差项均非正。最后一步仅交换有限求和顺序；括号为列和减行和。若网络平衡，该括号为零；一般情形取

$$
K=\sum_{i,j}a_{ij}\ge0
$$

即有各括号不超过 $K$，从而 $E'\le KE$。该常数只需统一控制所有列和减行和，不要求是最小可能值。

## 积分因子与比较结论

令 $F(t)=e^{-Kt}E(t)$。正时间上 $F'=e^{-Kt}(E'-KE)\le0$，而 $F(0)=0$。由连续性及单调性，$0\le F(t)\le F(0)=0$，故 $E(t)=0$，即 $x(t)\le y(t)$。证明只需零初始正部能量满足指数增长上界，无须一般状态下的能量单调下降。

## 三箱系统的实例

取

$$
(a_{ij})=\begin{pmatrix}0&0&0\\2&0&0\\1&3&0\end{pmatrix},
\qquad d=(1,0,0),\qquad f=(u,0,0).
$$

此时 $K=6$，方程为 $x_0'=u-x_0$、$x_1'=2(x_0-x_1)$、$x_2'=x_0+3x_1-4x_2$。若 $u\le1$，初值为零，则单位入口的显式解给出逐坐标上包络。令 $q=e^{-t}$，该解为 $Y_0=1-q$、$Y_1=(1-q)^2$、$Y_2=1-7q/3+3q^2/2-q^4/6$；在 $t=\ln2$ 时，$Y_2=19/96\approx0.198$。若另有 $u\ge0$，与零解比较还得到 $x\ge0$。$K=6$ 是能量估计中的增长常数，不是出口浓度的上界。

形式化源码为[DirectedNetworkComparison.lean](lean/DirectedNetworkComparison.lean)，其中分别给出一般比较、三箱应用及出口数值界；既有核验见[validation.json](validation.json)。本命题采用经典正系统比较方法，不主张比较思想的新颖性。
