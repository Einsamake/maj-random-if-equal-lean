# Maj-Random-If-Equal Lean formalization

目标：原无限二维同步四邻模型最坏扩展期望恢复时间 τ(N)=Θ(N²) 的自含Lean证明。**完整主定理尚未完成。**

当前经本地真实构建与标准 Lean --trust=0 验证：分析2321条定理、170个证明模块，共179份正式Lean源。核心另125条定理及1模型。定理条数不是完成百分比，独立AI审查不是人类专家认证。

已闭合真实连续边界/原Good、物理退出与二次缺失面积、真实joint历史及适应/渐进可测状态；原jointF退出停时版本AE等于physicalExit，保留∞law/扩展mean。一般依赖已揭示marks的非负AEfinite停时后single-site Exp(1)余等待与停时历史独立，actual exit∧T已证明finite并真正实例化。mask支持、正确D-relative面积势和精确被禁birth修正已证。真实next site-ring fairmark与停止σ独立及waiting联合尾已证，actual exit∧T真正实例化；仍缺完整future vector、物理补偿、自含CMST/FSS核心概率及最终二次主定理；不能使用masked恒漂移2捷径。

- [共同历史与渐进可测](formal/PROGRESS_2026-10-20_OBSERVED_HISTORY.md)
- [原jointF停时与残余等待](formal/PROGRESS_2026-10-21_MARKED_STOPPING.md)
- [实际面积势与有限率](formal/PROGRESS_2026-10-21_AREA_POTENTIAL.md)
- [真实停时后的新标记](formal/PROGRESS_2026-10-21_FRESH_MARK.md)
- [一般边界与原Good](formal/PROGRESS_2026-10-19_GENERAL_CONTOUR.md)
- [首次失守冻结端点law](formal/PROGRESS_2026-10-19_STOPPED_CLOCK.md)
- [跨时间路径](formal/PROGRESS_2026-10-19_TIME_CONSISTENCY.md)
- [物理首次失守时间](formal/PROGRESS_2026-10-19_PHYSICAL_EXIT.md)
- [方法账本](research/followup/METHOD_LEDGER_2026-10-21.md)
- [验证方法](docs/VERIFICATION.md)
- [形式化映射](formal/FORMALIZATION_MAP.md)

这是经审核的私有研究快照。工具链、依赖缓存、凭据、本机调度和私人会话状态不入仓；没有声明远端CI已重新构建。核心Lean4.35.0，分析Lean4.35.0-rc4，mathlib固定54c01c3314d33d15d77893cbe4e0472ff26bb34d。SNAPSHOT_MANIFEST.json逐文件记录大小与SHA256。
