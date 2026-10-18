# Maj-Random-If-Equal — Lean formalization in progress

研究目标：无限二维格点、同步四邻多数更新、公平独立随机平局的最坏扩展期望恢复时间 **τ(N)=Θ(N²)**。

**完整主定理尚未证明。本仓库是已通过内核检查的部分形式化及候选证明记录，不能作为开放问题已解决、原创性或人类专家认证的声明。**

当前验收（2026-10-18）：

- 分析部分：1953条定理，142个证明模块；核心部分：125条定理和1个模型声明。
- 共151份正式Lean源。新增保护演化与退出面积阶段62条定理。
- 统一构建及标准 `Lean --trust=0` 公理审计通过；依赖仅为 `Classical.choice`、`Quot.sound`、`propext`。
- 保留原模型、真实概率law、含∞恢复时间、原尺寸及exact-N量词。所有记录绑定实际源SHA256。

## 已闭合与尚缺部分

已建立模型/概率接口、调度比较的多个连接、原问题尺寸与期望定义、清理过程、实际格边/连续初态轮廓、周长与累计额外清理预算。最新阶段证明保护条件下角点删除后的连通/凸保持、真实事件索引停止轨迹的离散不变量，以及保护失守时净缺失面积至少L²/1600。

仍缺一般原Good连续几何的连接、真实物理停止law/生成元、CMST/FSS自含核心概率尾和最终二次主定理。独立AI审阅不等于人类专家审阅；辅助定理数量不是完成比例。

## 阅读

- [当前成果与精确边界](formal/PROGRESS_2026-10-18_PROTECTED_EVOLUTION.md)
- [有价值的方法、先行工作与失败路线](research/followup/METHOD_LEDGER_2026-10-18.md)
- [候选数学证明稿（未完整形式化）](research/followup/ca_clean_proof.md)
- [统一构建与源指纹](formal/audit/analysis-validation.json)
- [退出面积独立AI复核](formal/audit/exit-area-stage-semantic-review.md)
- [复现说明](docs/VERIFICATION.md)

## 依赖与来源

两个Lean工程使用不同工具链：核心4.35.0，分析4.35.0-rc4；分析mathlib固定为54c01c3314d33d15d77893cbe4e0472ff26bb34d。依赖、编译缓存及Lean二进制不存入仓库。历史draft为单独快照，不重复计入正式定理。

原问题：[Fatès–Marcovici–Taati, Question 7.4](https://arxiv.org/abs/2101.12682)。方法来源包括[CMST](https://arxiv.org/abs/1007.3599)、[Peres–Winkler](https://arxiv.org/abs/1112.0603)及[Liu–Yin](https://arxiv.org/abs/2111.04044)，具体适用边界见方法记录。不把已有工具当成本项目原创。

本仓库保留研究状态，不附加未经作者决定的开源许可。
