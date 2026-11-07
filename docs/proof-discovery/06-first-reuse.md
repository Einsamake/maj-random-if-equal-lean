# 三点有向环的序保持性

考虑 $i\in\mathbb Z/3\mathbb Z$ 上两组函数 $u_i,v_i$。假设它们在 $t\ge0$ 连续，在 $t>0$ 可微，并满足
$$
u_i'=\tfrac12(u_{i+1}-u_i)+f_i,\qquad
v_i'=\tfrac12(v_{i+1}-v_i)+g_i,
$$
其中指标按模3计算，$u_i(0)\le v_i(0)$ 且 $f_i(t)\le g_i(t)$。则 $u_i(t)\le v_i(t)$ 对所有 $i,t\ge0$ 成立。本命题以满足所列方程的函数为对象，不另行证明解的存在性。

令 $c_i=u_i-v_i$、$s_i=g_i-f_i$，则
$$
c_i'=\tfrac12(c_{i+1}-c_i)-s_i,\qquad s_i\ge0,\qquad c_i(0)\le0.
$$
由于三个指标按模3计算，循环移位 $i\mapsto i+1$ 是双射，故[有限置换比较原理](03-positive-energy.md)给出结论。[ReuseExample.lean](ReuseExample.lean) 中的 `three_cell_order` 形式化这一应用，无须使用原格点几何、协方差或时钟过程。

## 非双射映射的通量

双射性用于消去能量支持不等式右侧的求和。设两点集合上的映射 $\sigma$ 将两点均映到1，取向量 $a=(1,2)$，则
$$
\sum_{i=0}^1 2a_i^+(a_{\sigma(i)}-a_i)=2>0.
$$
因此该映射不满足同一未加权正部平方能量的耗散式；`nonbijective_flux_positive` 用精确算术核查了此值。该反例针对所用能量估计，不否定一般合作系统可能具有的序保持性质。

该文件的实际标准内核检查见[专项记录](reuse-validation.json)和[原始输出](reuse-kernel.log)。它是原267份正式源之外的独立实例，不增加或更改原主定理的封存计数。
