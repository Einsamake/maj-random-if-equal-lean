# Lean 工程说明

本目录包含二维同步四邻 Maj-Random-If-Equal 模型的形式化。完整渐近结论位于 [OriginalQuadraticRecovery](analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean)，原尺寸的最坏扩展期望定义位于 [OriginalRecoveryProfile](analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean)。

工程分为核心确定性部分和概率分析部分，分别使用 Lean `4.35.0` 与 `4.35.0-rc4`。正式源共267份，其中分析源259份、核心源8份。2026-10-26的最终阶段重新构建并审计分析工程；核心工程仅重核原源指纹与既有审计。

数学陈述见[结果](../docs/RESEARCH_RESULTS.md)，主要依赖关系见[形式化结构](FORMALIZATION_MAP.md)，构建命令与验证范围见[复现说明](../docs/VERIFICATION.md)。固定工具链及 mathlib 提交由工程文件指定，不应以当前默认版本替代。

`PROGRESS_*.md` 和 `audit/history/` 为按日期保存的历史记录；其中未闭合的接口应结合最终版本理解。当前说明与既有文稿审读指纹的关系见[版本约定](../docs/ARCHIVAL_RECORD.md)。
