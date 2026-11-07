# 版本状态

本页记录截至 2026-11-07 的公开材料范围。当前停止新增数学探索；本次整理不改动正式数学源及封存材料。

## 二维随机多数规则

原同步四邻多数规则的最坏扩展期望恢复时间满足 $\tau(N)=\Theta(N^2)$。尺寸 $N$ 是初始扰动的最小平移轴平行包围方形边长，优化对象为尺寸恰为 $N$ 的初态；恢复时间允许取无穷，结论覆盖两种纯色背景。

原主定理及其显示常数见 [OriginalQuadraticRecovery.lean](formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) 和[研究结果](docs/RESEARCH_RESULTS.md)。另行保存的 [phase2 下界](research/exploration/phase2/lean/ImprovedOriginalLower.lean)给出 $N\ge500001$ 时的 $\tau(N)\ge N^2/576000000$。

主定理的统一构建与标准 Lean 内核审计记录形成于 2026-10-26。其对应源码、指纹、工具链及独立复核范围见[验证方法](docs/VERIFICATION.md)；该日期的审计结论属于相应版本。

## 等待网络及公开范围

公开研究材料覆盖至 [phase12](research/exploration/phase12/validation.json)，包括随机等待表示、参数比较、完成时间辨识上界及路线标记规则下界。定理条件与证明入口见[研究结果](docs/RESEARCH_RESULTS.md)及[等待网络目录](research/exploration/README.md)。

本地工作区另有 phase13–phase19A 的验收记录；这些阶段的源码和数据未收入本公开版本。本公开版本的结果陈述以所收录文件为依据，历史页面中的后续计划按其撰写时点理解。

人类可读说明、形式数学源与既有审计分别标识版本。新整理的说明不继承旧稿的读者验收结论；当前说明的审读记录单独保存。
