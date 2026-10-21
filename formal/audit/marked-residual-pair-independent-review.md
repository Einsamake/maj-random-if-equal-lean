# 单格点残余等待与新标记完整联合分布：独立源码审查

当前：正式模块10条定理、11个命名声明逐原文语义、正式源码SHA与全部专项输出已独立核对。专项实际build0、标准Lean --trust=0审计0，仅标准三公理，零新Lean warning。正式SHA256：`ad4a5f022662d5bed6f14801d2ac60b865a93c0c63daf52654917b3e3227e140`。最终统一于 2026-10-21T20:46:21.454420+08:00 实际build0/标准trust0审计0；本代理逐项核完整183正式源集合及所有SHA、2371分析与126核心的全部2497项公理输出逐名逐序一致（含名称内撇号），并将四新模块50theorem/53named与统一源码绑定。核心沿用旧审计、8源SHA未变，未冒称本轮重编。独立AI检查不是人类专家认证；主定理尚未完成。

## 普通读者可读的意义

以后可以把“下一次还要等多久、下一枚硬币是什么颜色”作为一个整体使用，无需每次重新证明它们与过去的关系。这为后续累计更新影响准备了可直接调用的概率规律；它仍没有给出整块图的消退时间。

## 实际证明链

1. `waiting_event_factor`对任意可测A取G=E∩W⁻¹A。其中E确属R的停止历史，G只需在原样本空间可测，不要求G属于停止历史。它直接调用真实 `invariant_factor`：在各实际第一响候选中，翻转尚未揭示标记既保持E也保持W，因此保持G。
2. `waiting_event_mark_map`用Bool单点集合确定完整有限measure；`rectangle_factor`进一步取任意可测Bool事件，得到G与该标记事件的真正乘法因子。没有从两个边缘独立结论推联合独立。
3. `restricted_map_eq`接已验收的真实W在restrict E下的Exp(1)限制law，给任意Real×Bool矩形上的质量 μ(E)·Exp(A)·fair(B)。`Measure.ext_prod`要求的左侧有限measure由实际概率measure的限制及推前提供，不以停时有限性假装measure有限。
4. E=全样本空间得到实际完整pair HasLaw；对所有停止历史E保留限制law，再证明pair与整个停止σ独立。全程保留质量μ(E)，不除以μ(E)，故零概率历史事件无需额外分支。

## 假设、无穷值和实际实例

- 公平标记/任意等待事件的因子化，以及W与标记的IndepFun，只需R几乎处处有限，不要求R非负。草稿没有在这些地方冒称Exp等待律。
- 完整Exp(1)×fair联合law及其停止历史独立，另明确要求R在所有样本上非负；这恰是已验收等待定理的适用条件。
- R=∞或没有未来arrival时，原waiting的untopD总定义和nextMark=false回退均未被新定义偷换。law层面的排除依赖已有实际clock cofinality及AEfinite R，不把无穷观察时间直接转为0并声称有物理意义。
- 实际boundedExit两个实例分别给完整pair HasLaw及pair/停止历史独立。原定义先在ENNReal取min(exit,T)，再toReal，因而exit=∞时取T；真正finite、nonnegative、原历史stopping性由现有已证定理提供。没有假设未截断物理exit有限。

## 仍不在结论范围内

固定的是一个格点v；没有证明多格点残余向量、全局下一响竞争、完整未来随机字段、真实Poisson计数补偿/Dynkin、被禁止出生项的累计控制或CMST/FSS核心时间界。完整τ(N)=Θ(N²)主定理尚未完成。

正式、专项及最终统一证据现已全部独立核对并冻结。本次不修改Lean源码、不启动构建。
