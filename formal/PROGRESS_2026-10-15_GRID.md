# 无限格真实概率连接、对称性及确定时刻重启

更新：2026-10-15，北京时间。本轮于 **2026-10-15 12:25:29.270763+08:00** 统一验收成功：分析89模块、1108条公开定理、90份分析源，新增13模块157条。真实总构建及标准 `--trust=0` 公理审计退出0；最终独立核对98/98份源及1108/1108分析、126/126核心公理输出均一致。

本阶段连接原无限 `ℤ²` 与有限方形的完整随机轨迹、整场标记law、含 `∞` 的真实首达时间，并建立平移／标记补对称和确定时刻的实际同步重启。**完整最坏期望恢复时间 `τ(n)=Θ(n²)` 尚未形式化。**

## 有限方形和真实无限格

分析侧明确迁移四邻整数格模型并用rc4重新编译，没有跨工具链导入核心 `.olean`。更新只读north/east/south/west，不读中心；四输入真值数恰为二时读公平tie。支持封闭来自真实几何证明：原点半开方形外的点至多有一个内部邻点。

有限顶点是 `Fin(n+2)×Fin(n+2)`，嵌入整数格时坐标原样转换。extension先检查整数坐标处于 `[0,n+2)²`，再取有限下标，域外固定false；负坐标不会因 `Int.toNat` 被误当成原点。四方向越界输入、四输入计数及棋盘颜色均实际对齐。

`SquareGridEmbedding.synchronous_extend` 和 `alternating_extend` 证明任意确定全格marks下的**整个配置函数等式**，包含域外。再经 `extend_restrict` 覆盖任意满足实际Supported条件的无限初态，未将支持保持作为假设或只证明限制坐标。

`FairMarksTransport` 证明索引注入下整个独立公平乘积场的pushforward。`SquareGridLaw.restrictSample` 的索引是 `(v,j)↦(embed v,j)`；其真实law覆盖全部自然数时刻，不只单个硬币或有限前缀。无限配置的可测性逐坐标证明，有限Bool元组的可测性只用于局部规则，未把整个无限配置空间误当有限状态。

无限同步／交替首达时间与有限方形首达时间在restricted样本下逐样本相等，包含两侧都为 `∞` 的样本；由整场pushforward得到首达map和尾概率相等。零吸收性已证明，没有预设恢复有限。有限侧同步／时钟两向恢复尾比较因此传到原点方形的无限格初态。**时钟一侧仍为有限系统真实端点非零概率**，不能改称已构造了无限格连续时间吸收首达law。

## 平移和全一背景

平移采用 `translate a f(z)=f(z-a)`，将原点图案移到 `+a`。四方向与平移交换，整个同步轨迹和恢复law不变；奇坐标和平移会翻转棋盘颜色，交替phase相应翻转。随机样本索引为 `(z,j)↦(z-a,j)`，实际证明注入及整场测度不变，时间索引不变。

全一背景通过同时补状态和全部tie marks处理。四输入补对称给同步／交替完整轨迹恒等式；单公平硬币及整个乘积场的补映射均真保law。同步首次全一时间是真实 `ℕ∞` 变量，和补过程首次全零时间逐样本相等并保law。当前明确的全一目标首达law接口是同步版本，交替已有完整轨迹补恒等式；不声称固定同一硬币自动给互补轨迹。

## 实际未来独立和同步重启

`FairMarksPastFuture.past s` 只取已经使用的正时间槽 `1,…,s`。fresh future的零槽取旧的 `η(v,0)`，正槽j取 `η(v,s+j)`。索引注入、与实际past范围不交、整个future的原law和两场独立性均证明，包含s=0。这里所称过去不包含从未使用的零槽硬币；若把future零槽误取 `η(v,s)`，就会与past重叠。

当前状态经真实递推因子化到正槽past，因此可测且与fresh future独立。实际同步过程在确定时刻s可从当前状态重启，最大初态单调性与零吸收性给出非零事件包含于两个独立事件之交，故

\[
p_{n,f}(s+t)\le p_{n,f}(s)\,p_{n,\top}(t),
\qquad
p_{n,f}(jb)\le \bigl(p_{n,\top}(b)\bigr)^j.
\]

这里p是真实同步非零概率，也等于真实 `ℕ∞` 恢复尾；该块界可由已证有限↔无限law传到Supported无限初态。没有把Markov性、独立性、law或核心尾界作为新输入。底数仍是实际最大态概率，**尚未证明在二次尺度上存在统一的严格收缩 `q<1`**；幂次形式本身不等于已经获得严格几何衰减、期望有限或二次期望界。该阶段是确定时刻重启，不声称任意停时下完整未来向量强Markov。

## 新模块与验收

| 模块 | 作用 |
|---|---|
| `InfiniteGridModel` | 实际四邻整数格、颜色局部性、零保持及支持封闭 |
| `SquareGridEmbedding` | 四方向和颜色嵌入，完整同步／交替extension，任意Supported版本 |
| `FairMarksTransport`、`RecoveryTimeTransport` | 整场注入pullback law；含∞首达比较及等式 |
| `InfiniteGridRandomDynamics`、`InfiniteGridRecoveryTime` | 真实全格公平场、无限配置可测、实际扩展首达及吸收尾 |
| `SquareGridLaw` | 实际限制pushforward、完整随机配置、首达map／尾、两向clock尾及块尾连接 |
| `InfiniteGridTranslation`、`InfiniteGridTranslationLaw` | 一般平移、奇平移phase、整场及恢复law |
| `InfiniteGridComplement` | 状态与marks同时补、真保law、同步全一目标首达 |
| `FairMarksPastFuture` | 正槽过去、fresh future整场law及真实独立性 |
| `SquareDeterministicRestart`、`SquareRandomRestart` | 实际确定重启、当前／未来独立、乘法界及含∞恢复块尾 |

统一总入口实际构建和全部公开声明的显式 `lean --trust=0` 公理审计均退出0；仅标准 `Classical.choice`、`Quot.sound`、`propext`，无占位、自定义公理或内核绕过。本轮 `build_warning_lines=[]`；历史九项依赖提示保留于旧日志，未重置依赖。分析89模块1108条定理90源，与未改核心合计98源1233条辅助定理，计数包含迁移和基础引理，不表示完成比例。核心125条定理、模型定义及8源本轮未改，沿用2026-10-14 21:18:34的成功审计并核对哈希，不重复构建。上一分析基线为2026-10-14 21:50、76模块／951条定理／77源，保存在 `audit/history/2026-10-14-2150/`。

独立AI代理 `/root/independent_grid_audit` 未参与本轮Lean编写，逐项语义核对见 [复核报告](audit/infinite-grid-semantic-review.md)；最终独立复算98/98份源、1108/1108分析和126/126核心公理输出均一致，见 [指纹记录](audit/infinite-grid-semantic-validation.json)。独立AI意见不等于人类专家签署，Kernel通过不等于最终原命题严格等价已完成。改写前入口快照在 `../archive/docs/2026-10-15-before-infinite-grid/`；10月14日材料包原样保留，本轮另生成10月15日包。

## 接续缺口

1. FSS二维方岛上尾及CMST二维下尾的完整依赖图和自含Lean证明，尤其是二次时间尺度的实际严格收缩／下尾；引用文献或给核心结论参数不能代替证明。
2. 按 [原命题精确合同](ORIGINAL_STATEMENT_CONTRACT.md) 补首次H₂与首次正确背景的等价、最小包围方形边长和恰n最坏初态、任意有限扰动归一化、小尺寸及N与有限参数N−2、扩展期望和上确界量词；该合同尚非Lean实现。
3. 在真实核心尾成立后，接已证明实际确定时刻重启和含∞块尾，取得扩展期望有限、二次上下界及统一常数。
4. 最终完整Lean主定理和原始数学命题的严格等价及完整验收。

本阶段已关闭的真实随机连接、平移／背景和确定重启不再重复列为未证明。详见 [NEXT_PHASE](../README.md)。完整工程仍沿用 [粗估口径](../research/followup/PROGRESS_ESTIMATE_2026-10-14.md) 剩余约70%、宽范围55%—90%；需先展开FSS／CMST深依赖再重估，不按新增辅助定理机械扣减。
