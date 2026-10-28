# 当前状态

截至 2026-10-28，最近一次完整验收为 phase12。

原二维同步四邻多数规则的最坏扩展期望恢复时间满足 $\tau(N)=\Theta(N^2)$，$N$ 是初始有限扰动的最小平移轴平行包围方形边长。主定理同时覆盖两种纯色背景，恢复时间允许取无穷。原有显示常数及范围见[结果与验证](docs/RESEARCH_RESULTS.md)；[后续下界](research/exploration/phase2/lean/ImprovedOriginalLower.lean)将其改进到 $N^2/576000000$，适用于 $N\ge500001$。

259 份分析源完成统一构建与标准 `--trust=0` 审计；8 份核心旧源复核了既有指纹及审计，本轮未重编。记录见[主定理进展](formal/PROGRESS_2026-10-26_MAIN_THEOREM.md)与[验证方法](docs/VERIFICATION.md)。审计使用标准 Lean 内核及 `--trust=0`，公理输出仅包含 `propext`、`Classical.choice`、`Quot.sound`。这不是人类专家审稿或模型对应关系的认证。

独立等待网络的概率表示、参数比较和辨识结论见[结果与验证](docs/RESEARCH_RESULTS.md)。截至现有记录，探索完成至 [phase12 验证](research/exploration/phase12/validation.json)，[phase11 验证](research/exploration/phase11/validation.json)亦已通过；下一步是连接实际分支计数的分布并收紧有限尾界，尚未完成。详见[探索入口](research/exploration/README.md)。
