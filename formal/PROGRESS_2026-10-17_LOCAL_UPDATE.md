# 真实局部更新、清理与全轨迹周长预算：已统一验收

分析136模块／1891条公开定理／137源；核心125条定理及1模型、8源未变，共145份正式源、2016条辅助定理。本轮新增8模块93条定理。统一构建与标准Lean --trust=0公理审计退出0（2026-10-17T10:28:33.974191+08:00）；全部98个新命名声明另逐项审计通过，仅Classical.choice、Quot.sound、propext。无占位、自定义公理或内核绕过，新源码无Lean警告，保留既有batteries本地修改提示。

| 新模块 | 公开定理数 |
|---|---:|
| ConvexLocalUpdate | 16 |
| ConvexBirthUpdate | 18 |
| GridCleanupDeletion | 11 |
| ConvexCleanupUpdate | 8 |
| CleanupConnectivity | 6 |
| GridPerimeterUpdate | 13 |
| GridPerimeterDynamics | 16 |
| ClippedPerimeterBudget | 5 |

行列凸且稳定的实际有限负自旋集合，其真实rawStep发生改变时只可能degree=2平局：空位tie=true出生，已占据点tie=false死亡。actual modifiedStep分类保留真实cleanup，没有把它替换成任意字段。上一轮8条standalone draft已纳入正式模块扩至16条，此处按完整统一记录计数。

出生一支已闭合：degree2空位必有一水平、一竖直占据邻点，插入保持行列整数区间凸、稳定和四邻连通，cleanup不再删除点；横纵实际坐标投影集合都不变。该结论不覆盖degree2死亡。

合法degree<2清理删除及任意合法链保持行列凸和四邻连通，进而真实cleanup也保持这些性质。删除侧另给精确条件：Stable S时erase v稳定恰为各占据邻点原degree≥3；conditional双删结果以所有存活点的明确原degree余量为前提，再由实际合法删除和终态唯一性识别cleanup。没有证明原Good几何自动提供该余量。

周长始终是真实暴露单位侧边数。任意有限S的插入满足P(insert v S)+2degree(S,v)=P(S)+4；删除满足P(erase v S)+4=P(S)+2degree(S,v)。真实多数raw/masked/modified Step与Word的P都非增，无Stable、凸性或Good前提。每个严格清理删除至少降低P两单位，沿真实状态递归的额外清理总删点数wordLoss满足 P(final)+2wordLoss≤P(initial)。这不把raw死亡算进额外清理。

对实际clip初态得到P(final)+2wordLoss≤8L+4、wordLoss≤4L+2。ClippedPerimeterBudget使用既有真实ClockEventWord.word及身份fair marks，clockOccupied的有限配置精确等于DropletClockLaw.endpoint true。预算点态适用于该真实改造过程每个物理端点，未将它冒充原raw过程的预算或停止链／生成元／二次恢复尾。

[统一证据](audit/analysis-validation.json)、[全部新增命名声明](audit/update-stage-declarations-validation.json)、[独立审阅](audit/update-stage-semantic-review.md)、[独立指纹证据](audit/update-stage-independent-evidence.json)、[反例和后续路线](audit/update-stage-route-review.md)。旧128 proof模块及8核心源不变。独立AI不冒充人类专家，条数不是完成率。

完整τ(N)=Θ(N²)主定理仍未完成。一般GeometricGood与离散凸/连通等价、实际大保护域排除死亡细颈、一般Good保持、角点漂移和首退出已删面积、物理停止演化／生成元、自含CMST/FSS核心尾与最终常数仍缺。相邻degree2死亡也可能断连通，L=1可出现一次总删3点，见独立反例；不能将出生或legal cleanup结论误用于raw degree2死亡。
