# 居中清理、不同区域比较与真实时钟端点阶段

2026-10-16。用户最新“继续”恢复主证明，本阶段完成后先停止；自动调度保持PAUSED。工作区已迁移到 `<workspace>`。**完整原主定理τ(N)=Θ(N²)尚未完成。**

## 本轮证明

| 模块 | 新定理 | 实际结论 |
|---|---:|---|
| CenteredPeelingTransport | 26 | 有限顶点邻接／degree与居中整数格逐点对应；合法Delete／Deletes、稳定性及终止清理结果交换；实际cellUpdate后finiteCleanup与无限格cleanup的单步及整word动态共轭 |
| DropletDomainComparison | 29 | 在S⊆D⊆E和S⊆T下，同一site/tie事件字的改造D过程被原E过程包含；扩展事件索引首缺失≤raw恢复索引；冻结只在首缺失之前比较状态 |
| DropletClockLaw | 15 | 从实际时钟与公平标记乘积测度推出端点可测、真实字fiber因子化和无条件可数混合；接实际finiteModifiedWord；给出物理t时的点态／概率比较 |
| WholeSquareClockTransport | 8 | centeredSites上的raw字等于原MarkedEventTrace执行，端点逐样本及law等于ClockExecutionLaw.endpoint；将物理t的失败事件比较实例到原真实过程与剪角改造过程 |

新增共78条定理及23个定义／缩写／实例，四模块全部101个声明另逐项 `--trust=0` 审计；没有以目标law、独立性、面积漂移或核心尾作参数。旧101个分析proof modules和8份核心源码未变，仅总入口新增导入。

## 严格时间、标记和边界

clock word按较新事件在前存储，执行恰好reverse一次；每条记录保留(vertex,响铃索引)身份，从同一个实际fair field读取tie。每个有限方形顶点的时钟速率为1，mask外事件恒等，未按总顶点数归一化时间。空fiber与null-set总化fallback均保留；全字law包含所有List事件字。

对固定word w，已推出真实乘积测度上的联合式：额外可测clock事件E与w的fiber上的端点概率，等于clock事件概率乘以fresh有限公平向量的执行law。再由可测不交word分割，推出无条件端点law是该乘积的可数和。fresh向量law不是假设。

L≥1时，有限cleanup经真实邻接、合法删除链及既有终态唯一性搬运；实际单步是SquareSpin.cellUpdate后占据集合的finiteCleanup，mask外恒等。整word共轭适用于任意有限初态，不偷加稳定或clipped支撑前提。

通用DropletClockLaw的D/E参数并未要求落在方形内，因此一般定义只表示给定有限vertex clocks驱动的set-word输出在该方形的restriction。真正使用的D=clippedDomain、E=centeredSites有完整几何连接；不能把任意D/E参数解释成所有域内点都有时钟。

## 实际失败事件比较

在L≥1、S⊆clippedDomain、S⊆image(occupied g)、非空有限保护顶点I下，任意物理时刻t满足：

```text
P(original ClockExecutionLaw.endpoint(t,g) = allFalse)
  ≤ P(存在 v∈I，clipped modified endpoint(t,S,v) = false).
```

这里较大过程确实逐样本等于此前已构造的原零边界有限方形时钟过程，而非另写同名动态。较小过程在真实clip mask内部执行heat-bath＋cleanup。I目前仍是通用非空顶点集，尚未具体化CMST的内域D与外邻边界∂D之并。

首次缺失的ℕ∞定义是**事件索引**，没有将索引当物理时间。冻结后的状态只在首退出之前断言支配；没有推出停止后全路径支配。物理t的比较只涉及未冻结端点与失败事件，没有宣称停时整过程law、Markov或生成元。

## 验收和证据

分析105模块／1411条公开定理／106源；核心125条定理及1个模型定义、8源未变，共114份正式源、1536条辅助定理。本阶段新增4模块78条定理。 2026-10-16T23:00:13.658877+08:00统一构建与标准 `--trust=0` 公理审计退出0，仅 `Classical.choice`、`Quot.sound`、`propext`，无占位、自定义公理或内核绕过。新Lean源码无警告；构建保留一条既有batteries仓库本地改动提示。

分析使用Lean4.35.0-rc4、固定mathlib `54c01c3314d33d15d77893cbe4e0472ff26bb34d`，实际命令为 `lake build` 和 `lake env lean --trust=0 AnalysisAxioms.lean`。核心8源指纹不变，沿用2026-10-14的Lean4.35.0成功审计。指纹绑定见 [统一记录](audit/analysis-validation.json)，新模块个别审计见 `audit/centered-peeling-transport-*`、`droplet-domain-comparison-*`、`droplet-clock-law-*`、`whole-square-clock-transport-*`。

[独立AI语义报告](audit/modified-clock-semantic-review.md) 与 [全部源／声明证据](audit/modified-clock-independent-evidence.json) 由未编写本轮Lean的审阅代理生成；不是人类专家认证，也不是完整主定理等价验收。条数不是完成比例。

## 剩余

仍缺Good简单轮廓及更新不变性、CMST内域与外邻边界之并的具体保护集合、首退出前已删面积、从真实过程导出生成元／所需停止过程关系、自含FSS上尾和CMST下尾、二次尺度严格收缩常数及最终二次扩展期望。端点的真实law不自动给出有限生成元或停止过程演化；已有四向块基数不等于首退出前已删面积；2-core不等于Good。已有块幂尾仍无二次尺度底数统一<1，不能宣称一般期望有限。

下阶段见 [NEXT_PHASE](../README.md)。本轮已停止，不恢复自动唤醒，不操作独立工具探索聊天。
