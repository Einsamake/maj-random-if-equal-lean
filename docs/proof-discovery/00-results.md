# 恢复时间定理

令 $X_t$ 为 $\mathbb Z^2$ 上的二色同步过程。格点在时刻 $t+1$ 取其四邻在时刻 $t$ 的多数颜色；平票使用在格点和轮次间独立的公平标记。固定纯色背景 $\beta$，初态与背景不同的格点组成有限集合 $A$，首次回到背景的同步轮数记为 $T_{A,\beta}\in\mathbb N\cup\{\infty\}$。

扰动尺寸是包含 $A$ 的最小平移轴平行格点方形的边长。等价地，寻找最小 $N$ 使
$$
A\subseteq [a,a+N)\times[b,b+N)
$$
对某些整数 $a,b$ 成立，其中只取整数格点。例如 $A=\{(0,0),(2,1)\}$ 的尺寸是3，而点数是2。

令 $\tau(N)$ 为两种背景、尺寸恰为 $N$ 的初态之扩展期望 $\mathbb E T_{A,\beta}$ 的上确界。有限非空尺寸可由平移归一到有限模式集，故最大值可实现；边界情形的处理见[原轮廓定义](../../formal/analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean)。

原封存定理给出
$$
\frac{N^2}{56623104000}\le \tau(N)\le664066N^2,
\qquad N\ge786432000.
$$
上界单独对 $N\ge16$ 成立。[后续定量改进](../../research/exploration/phase2/lean/ImprovedOriginalLower.lean)将下界改为 $N^2/576000000$，适用于 $N\ge500001$。

下界由一族实心初态实现，估计从加速辅助过程的保护失守概率导出；上界对所有相应尺寸的初态成立，使用局部清空、同步比较和统一重启。结论控制最坏期望，并非对每条轨迹给出确定性恢复时限。主定理允许无穷值作为首达时间的可能取值，有限期望由上界推出。

主声明为 [OriginalQuadraticRecovery](../../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) 中的 `tau_theta_quadratic`。数学论证见[辅助过程与比较](01-route.md)，机器检查范围见[验证说明](../VERIFICATION.md)。
