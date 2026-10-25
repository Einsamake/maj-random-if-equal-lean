# Lean验证与材料

目标为原无限二维同步四邻 Maj-Random-If-Equal 最坏扩展期望恢复时间 τ(N)=Θ(N²)。**完整主定理尚未完成。**

分析224个证明模块、2993条辅助定理、225份分析源；核心旧125条定理及1模型、8源未变且未重编。合计233份正式源、3118条辅助定理与1个模型，3119项实际公理输出。最新统一build与标准Lean --trust=0逐定理审计均退出0（2026-10-25T20:35:07.662832+08:00）；仅Classical.choice、Quot.sound、propext，零新增Lean warning。

核心目录formal/使用Lean4.35.0；分析目录formal/analysis/使用Lean4.35.0-rc4及mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d。沿用formal/.tools/编译器和各自.lake缓存，不跨版本复用olean，不重装依赖。

从工作区根目录用现有Python运行formal/scripts/validate_analysis.py：实际统一build，再lake env lean --trust=0 AnalysisAxioms.lean逐项审计；JSON绑定完整source集和SHA256。新增阶段脚本另覆盖def/abbrev/命名instance，日志和独立审查在audit/。核心125 theorem+1model的原验收见audit/core-validation.json，当前8源hash不变。仅batteries docs/README.md既有local change warning，无新增Lean warning。

[形式化对应与边界](FORMALIZATION_MAP.md) · [共同历史](PROGRESS_2026-10-20_OBSERVED_HISTORY.md) · [原F停时](PROGRESS_2026-10-21_MARKED_STOPPING.md) · [实际面积势函数](PROGRESS_2026-10-21_AREA_POTENTIAL.md) · [下一阶段](../README.md)

scripts/validate_workspace.py核对正式source集/hash、脚本语法与文档链接；formal/scripts/package_lean.py只在验收source完全匹配时打包，并逐文件读回ZIP大小/hash及CRC。drafts保留研究草稿，不属于正式定理计数。私有审核快照由scripts/sync_private_repository.py准备，凭据、缓存、本机调度不上传；它不会自行commit/push。

[真实停时后的新标记](PROGRESS_2026-10-21_FRESH_MARK.md)。

[实际计数与精确均值](PROGRESS_2026-10-21_CLOCK_MEAN.md)。


[真实逐次响铃的可预测补偿](PROGRESS_2026-10-22_PREDICTABLE_COMPENSATION.md)：新增3模块24定理/29命名声明；仅在标准原历史可预测σ上比较真实事件测度与时间参考测度，不是全ambient积σ等价。更新前真实状态与物理面积Dynkin现已闭合，见23日验收。


[23日真实前态、面积Dynkin与clipped生成元](PROGRESS_2026-10-23_AREA_DYNKIN.md)。原finite-clock辅助过程已给真实物理时间面积公式；主定理及定量CMST/FSS尚未完成。


[24日：真实清理总预算、早退出概率与零权边界层](PROGRESS_2026-10-24_CLEANUP_WEIGHT.md)。

[25日：实际加权线性率与平方时间概率界](PROGRESS_2026-10-25_QUADRATIC_CLOCK_TAIL.md)。真实CLOCK结论已供给数值界；原同步τ(N)=Θ(N²)仍未完成。

[25日：原同步与exact-N二次期望下界](PROGRESS_2026-10-25_SYNC_LOWER.md)。这只完成Θ定理的下界。

[25日：混合边界与真实阶梯形clock基础](PROGRESS_2026-10-25_MIXED_BOUNDARY.md)。这部分尚不给恢复时间上界。

新增行长编码11定理见[YoungRows](PROGRESS_2026-10-25_YOUNG_ROWS.md)；粒子编码/二次上界仍未完成。

[粒子编码与有限算子最新验收](PROGRESS_2026-10-25_EXCLUSION.md)：真实clock矩方程与二次上界仍未证明。
