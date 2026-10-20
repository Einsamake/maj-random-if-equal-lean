# Lean验证与材料

目标为原无限二维同步四邻 Maj-Random-If-Equal 最坏扩展期望恢复时间 τ(N)=Θ(N²)。**完整主定理尚未完成。**

分析170个证明模块、2321条辅助定理、171份分析源；核心125条定理及1模型、8源未变。合计179份正式源、2446条辅助定理与1个模型。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-21T05:39:35.916899+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，未冒称本次重编。

核心目录formal/使用Lean4.35.0；分析目录formal/analysis/使用Lean4.35.0-rc4及mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d。沿用formal/.tools/编译器和各自.lake缓存，不跨版本复用olean，不重装依赖。

从工作区根目录用现有Python运行formal/scripts/validate_analysis.py：实际统一build，再lake env lean --trust=0 AnalysisAxioms.lean逐项审计；JSON绑定完整source集和SHA256。新增阶段脚本另覆盖def/abbrev/命名instance，日志和独立审查在audit/。核心125 theorem+1model的原验收见audit/core-validation.json，当前8源hash不变。仅batteries docs/README.md既有local change warning，无新增Lean warning。

[形式化对应与边界](FORMALIZATION_MAP.md) · [共同历史](PROGRESS_2026-10-20_OBSERVED_HISTORY.md) · [原F停时](PROGRESS_2026-10-21_MARKED_STOPPING.md) · [实际面积势函数](PROGRESS_2026-10-21_AREA_POTENTIAL.md) · [下一阶段](../README.md)

scripts/validate_workspace.py核对正式source集/hash、脚本语法与文档链接；formal/scripts/package_lean.py只在验收source完全匹配时打包，并逐文件读回ZIP大小/hash及CRC。drafts保留研究草稿，不属于正式定理计数。私有审核快照由scripts/sync_private_repository.py准备，凭据、缓存、本机调度不上传；它不会自行commit/push。

[真实停时后的新标记](PROGRESS_2026-10-21_FRESH_MARK.md)。
