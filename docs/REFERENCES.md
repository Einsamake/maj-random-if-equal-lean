# 文献与出处

<a id="fates-marcovici-taati-2022"></a>

## Fatès–Marcovici–Taati 2022

[1] N. Fatès, I. Marcovici and S. Taati. *Self-stabilisation of cellular automata on tilings*. Fundamenta Informaticae, **185**(1), 2022. DOI: [10.3233/FI-222103](https://doi.org/10.3233/FI-222103). [arXiv:2101.12682v3](https://arxiv.org/abs/2101.12682v3), 2022-03-05.

该文第4.2节定义同步四邻 Maj-Random-If-Equal 规则；命题4.1给出至多三次的稳定化时间界。第7.2节问题7.4询问其精确稳定化速度，并提出二次尺度的猜想。本仓库以该版本的问题和模型为背景。

连续时间更新在该文例4.3中另行讨论。其时间参数及更新机制与同步轮次不同；本仓库使用辅助时钟过程时，另行证明与原同步过程的比较。此出处不构成对当前文献优先权的全面调查。

## 形式化结果的引用

原渐近定理为 `MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic`，源码位于 [OriginalQuadraticRecovery.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean)。显示常数、参数域与后续定量改进见[结果](RESEARCH_RESULTS.md)；工具链与源版本见[验证说明](VERIFICATION.md)。

引用仓库时，应同时记录仓库地址、所用提交及具体声明。2026-10-26的封存材料另由[材料清单](../deliverables/README.md)标识；封存材料的日期不等同于期刊发表日期。网络研究各命题的出处在[研究目录](../research/exploration/README.md)逐项列出。
