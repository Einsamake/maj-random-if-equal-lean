# 端点轨迹的比较证明与有理数界

沿用[正文](README.md)的方程、固定参数范围、零初值及给定经典解条件。$x$ 为任意允许解，$Y$ 为四个上端速率和单位入口下的显式解。正文已计算残差 $R_i=Y_i'-F_i(Y,u)\ge0$。

## 非严格上解的比较

取任意 $\varepsilon>0$，令 $h(t)=\varepsilon e^t$、$Z_i(t)=Y_i(t)+h(t)$。共同增加 $h$ 不改变两个浓度的差，故

$$
\begin{aligned}
Z_0'-F_0(Z,u)&=R_0+(1+a)h>0,\\
Z_1'-F_1(Z,u)&=R_1+h>0,\\
Z_2'-F_2(Z,u)&=R_2+h>0.
\end{aligned}
$$

初始时 $x_i(0)=0<Z_i(0)=\varepsilon$。若之后出现接触或越界，在一个出现接触或越界的有限闭时间区间内，零点集合闭且不含零时刻附近的一段区间；再利用坐标数有限，可取所有坐标中的首次接触时刻 $s>0$。存在坐标 $i$ 满足 $x_i(s)=Z_i(s)$，而所有坐标仍有 $x_j(s)\le Z_j(s)$。

令 $w_i=x_i-Z_i$。对充分小的 $h>0$，有 $[w_i(s)-w_i(s-h)]/h\ge0$。在正时刻 $s$ 导数存在，令 $h\downarrow0$ 即得 $w_i'(s)\ge0$。另一方面，接触坐标自身相等，其余坐标的耦合系数非负，因此

$$
w_i'(s)=F_i(x(s),u(s))-Z_i'(s)
\le F_i(Z(s),u(s))-Z_i'(s)<0,
$$

矛盾。于是 $x_i(t)<Z_i(t)$。固定 $t\ge0$，令 $\varepsilon\downarrow0$，得到 $x_i(t)\le Y_i(t)$。严格上抬消除了直接首次接触论证中可能出现的相切缺口。形式化证明复用一般矩阵比较定理；本段为当前三箱方程的初等论证。

## 十九次幂比较

令 $q_*=e^{-(21/19)\ln2}$，则 $0<q_*\le1$ 且 $q_*^{19}=2^{-21}$。源码核验的整数不等式

$$
929^{19}2^{21}\le2000^{19}
$$

等价于 $(929/2000)^{19}\le q_*^{19}$。非负数的十九次幂严格递增，故 $929/2000\le q_*$。这里不使用浮点数近似确定不等号。

对 $p(q)=1-7q/3+3q^2/2-q^4/6$，有

$$
p'(q)=-\frac{(1-q)(7-2q-2q^2)}3.
$$

在 $[0,1]$ 上，$1-q\ge0$ 且 $7-2q-2q^2\ge3$，故 $p'\le0$。代入 $q_*$ 的下界于是给出 $p(q_*)$ 的上界：

$$
x_2(t_*)\le p(q_*)\le p(929/2000)
=\frac{7425545410773}{32000000000000}
<\frac{233}{1000}<\frac{24}{100}.
$$

源码：[EndpointArithmetic.lean](lean/EndpointArithmetic.lean)、[EndpointCertificate.lean](lean/EndpointCertificate.lean)、[EndpointTank.lean](lean/EndpointTank.lean)。[既有验证记录](validation.json)。
