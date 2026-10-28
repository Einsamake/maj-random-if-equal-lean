# 结果与验证入口

## 二维多数规则

在无限二维整数格上，所有格点同步按上、下、左、右四邻居的上一轮颜色更新：多数决定颜色，平票时以独立公平随机选择决定。中心格不投票。初态为纯色背景上的有限异色集合 $A$；黑底白扰动与白底黑扰动都包括在内，且平票选择在格点和轮次之间相互独立。

令 $T_A$ 为首次回到纯色背景的轮数；若从不回到纯色，令 $T_A=\infty$。$\operatorname{size}(A)$ 是包含 $A$ 的最小平移轴平行方形的格边长，而不是 $|A|$。记

$$\tau(N)=\max_{\operatorname{size}(A)=N}\mathbb E[T_A],$$

其中期望允许取无穷。已证 $\tau(N)=\Theta(N^2)$。具体界为

$$\frac{N^2}{56623104000}\le\tau(N)\le664066N^2\qquad(N\ge786432000),$$

右侧上界单独对 $N\ge16$ 成立。[主定理源码](../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean)的 `tau_theta_quadratic` 是渐近结论入口；[主定理进展](../formal/PROGRESS_2026-10-26_MAIN_THEOREM.md)记录显示界和证明依赖。下界由实心方块提供，上界覆盖所有同尺寸初态。原证明及封存结果之外，[后续证明](../research/exploration/phase2/lean/ImprovedOriginalLower.lean)还给出 $N\ge500001$ 时的下界 $N^2/576000000$；见[说明](../research/exploration/phase2/README.md)及[验证](../research/exploration/phase2/validation.json)。

## 独立网络与观测问题

[探索入口](../research/exploration/README.md)给出独立等待网络的定义、与三箱出口的联系、参数盒最大值及辨识结果，并逐项链接证明和验证。尤其是在同一组 100 次条件独立任务上，完成时间规则的统一成功率上界与一条路线标记规则的成功率下界分别为 $353/606$ 和 $33/50$。两者是不同方向的界，不是两个实测准确率；完整条件和推导见[观测对照](../research/exploration/phase12/README.md)。

## 证据范围

259 份分析源完成统一构建与标准 `--trust=0` 审计；8 份核心旧源复核了既有指纹及审计，本轮未重编。声明公理输出和工具链记录见[验证方法](VERIFICATION.md)与[主定理进展](../formal/PROGRESS_2026-10-26_MAIN_THEOREM.md)。记录显示标准 Lean 内核 `--trust=0` 审计通过，公理输出仅为 `propext`、`Classical.choice`、`Quot.sound`。后续探索各有独立验证记录，最新见 [phase11](../research/exploration/phase11/validation.json) 和 [phase12](../research/exploration/phase12/validation.json)。形式化检查不证明自然语言模型与形式模型的对应已获人类专家认可，也不证明结果的新颖性。模拟本科读者的反馈用于改善解释，不是人类用户测试或专家评审。

问题背景：[Fatès、Marcovici、Taati，Question 7.4](https://arxiv.org/html/2101.12682v3)。[原证明复盘教程](proof-discovery/README.md)提供图解和算例。
