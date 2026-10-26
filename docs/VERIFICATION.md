# 完整主定理验证记录

分析258个证明模块、3280条辅助定理、259份分析源；核心旧125条定理与1模型、8源仅回核指纹未重编。共267份正式源、3406项实际公理输出。最新分析统一构建及标准Lean --trust=0审计实际退出0（2026-10-26T14:53:59.002869+08:00），仅三个标准公理，零新增Lean警告。

主定理为 `MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic`：对原无限二维同步四邻模型，取两种纯色背景、尺寸恰为 N 的最坏扩展期望，证明所有充分大的 N 都满足两侧二次界。上界对 N≥16 成立；两侧共同阈值为 N≥786432000。这组显示常数不声称覆盖所有 N≥1。最终参数中没有保留待证的概率界或耦合假设。

分析使用Lean4.35.0-rc4与固定mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d；核心使用Lean4.35.0，本轮仅核旧八源及审计，不跨版本复用olean，也未重置缓存依赖。本次两阶段18新模块107定理126具名声明有各自build0和标准trust0审计；统一267源的指纹和3406实际公理输出由独立脚本重算绑定。仅三个标准公理，零新增Leanwarning，仅原batteries文档提示。

[完整结果与源指纹](../formal/PROGRESS_2026-10-26_MAIN_THEOREM.md) · [最终独立语义](../formal/audit/original-theta-independent-review.md) · [完整绑定](../formal/audit/original-theta-independent-final-binding-evidence.json) · [统一记录](../formal/audit/analysis-validation.json)。

复现分析验证：在工作区根目录用现有 Python 运行 `formal/scripts/validate_analysis.py`，它先实际统一构建，再执行 `lake env lean --trust=0 AnalysisAxioms.lean`。专项脚本还审计新增定义和具名声明。`scripts/validate_workspace.py` 核对源指纹、脚本语法和文档链接；它不重编证明。`formal/scripts/package_lean.py` 逐文件核对材料 ZIP 及其 CRC。

独立AI复核不等于独立人类专家确认；本地验收不冒充远端CI，也不认证全球新颖性。日期较早的PROGRESS和研究候选稿保留历史状态，不代替本次精确主定理。
