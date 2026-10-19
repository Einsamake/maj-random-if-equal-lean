# 剪角域与改造有限事件字：独立 AI 语义审阅

审阅者：`/root/clipped_independent_audit`，未参与本阶段 Lean 证明编写。日期：2026-10-16。本代理只读 Lean，未重复启动构建；本报告不构成人类专家认证。

**本阶段语义、统一内核记录及全源证据已独立核对，未发现所审范围内的具体漏洞。**

## 来源与审阅范围

已直接读取 [CMST v2, §8](https://arxiv.org/html/1007.3599v2)，核对式 (8.2)、Definition 7、改造更新、式 (8.5)、(8.8)–(8.9)。论文采用居中方形与半径 `L+1` 的 L¹ 菱形交；负自旋多数清理在单次热浴更新后执行，内域首次缺失时停止。Good 另含简单轮廓、周长和内域约束。这些来源事实只界定阶段语义，不作为 Lean 公理或概率界输入。

本阶段实际证明对象是确定性的有限剪角域、四向方块计数、同标记热浴与清理事件字，以及真实有限方形的坐标和 raw 更新对应。它不包括停止改造随机链、Good 不变性、首次退出面积损失或二次尾界。下面的逐项判断来自本代理对实际 Lean 定义和证明的只读核对。

## 定义、端点及真实规则

| 对象 | 实际源码与语义核对 |
| --- | --- |
| 剪角域 | `clippedDomain L` 是有限整数区间乘积经 L¹ 条件过滤，`mem_clippedDomain` 给出与 `|x₁|≤L ∧ |x₂|≤L ∧ |x₁|+|x₂|≤L+1` 的严格等价；包含坐标端点，无浮点近似。 |
| 基点范围 | `boundaryBand` 使用 `10*(|x₁|+|x₂|)≤9*L+10`。这是包含相关外邻点的较大带，而非把所有带内点都定义为真正边界；本阶段未证明原文首次退出点落在此带的完整轨迹命题。 |
| 方块与下界 | `blockPoint` 的各偏移为 `Fin (L/20)` 的值加1，范围是1至自然数商 `L/20`；映射单射，故方块恰有 `(L/20)^2` 点。`L≥40` 时，三角不等式及取整算术得到整块落在真实剪角域，实数平方下界为 `L²/1600`。没有把自然数商误作实数商。 |
| 四个朝向 | `reflect` 分别翻转两个坐标的符号，证明为对合并保持域与带。`directedBlock` 在反射后的基点构造东北块再反射回来，`mem_directedBlock` 明确得到以原基点为中心的四种有符号偏移；不是仅反射点集而遗忘基点。 |
| 初始稳定 | `toward` 在非零坐标向0走一步，在0处走+1；`L≥1` 保证这两个分别沿水平、垂直方向的邻点仍在域内。两点互异，故每个域内点至少有两个域内真邻点，推出实际 `clippedDomain_stable` 及 cleanup 恒等。稳定性不是未经证明的输入；不覆盖错误的 `L=0` 单点稳定命题。 |
| 实际热浴 | `localRule` 只读北东南西四个邻点，tie 是事件自带的 Boolean。`state_rawStep` 证明插入／擦除恰为一次函数写回，`rawStep_actual_marks` 又接任意给定整场 marks 在该事件点时刻的值。没有读取中心点或擅自改变 tie。 |
| mask 外事件 | `maskedRawStep` 与 `modifiedStep` 都先判断更新点是否属于 mask；外部直接返回原状态，内部才热浴并在改造侧 cleanup。因此在不稳定状态下也没有域外事件引起的额外清理。 |
| 同标记支配 | 集合包含通过实际 Boolean 顺序接 `majority4_monotone`；同一个点、同一个 tie 下原更新单调，cleanup 收缩且单调。因此改造单步及有限字被原更新字包含。假设只涉及真实起始包含，不包含欲证概率尾界。 |
| 执行次序 | `rawWord`、`modifiedWord` 对列表从左到右递归；与 `foldl` 等价，append 定理保持先前缀后后缀。比较使用完全同一个 `List (Site × Bool)`，没有更改事件顺序或重采样标记。 |
| 支撑与稳定保持 | 原和改造有限字都保持 mask 支撑；任意稳定初态的改造字保持2-core稳定。结合已证真实初始域稳定性，`initial_clippedWord_stable` 不再接受外加稳定性假设。 |

## 与现有有限方形的精确连接

`parameter L = 2*L-1`，`side L = 2*L+1`，在 `L≥1` 时证明 `parameter L + 2 = side L`。`recenter` 将真实 finite vertex 的坐标各减 L；`uncenter` 各加 L。证明嵌入单射、居中方形与原半开 `Inside` 完全等价、每个居中格点均有原 finite vertex，以及边长平方的精确计数。需要尺寸等式的结论显式保留 `L≥1`；没有把 `L=0` 的截断自然数减法当作相同边长。

`recenterConfig` 是原有限配置先零扩展、再按 `(-L,-L)` 平移；`recenterConfig_at_vertex` 和 `recenterConfig_outside` 核对平移符号及全部域外 false。实际 `clippedVertices` 的 `recenter` 像恰等于 `clippedDomain`，不是另一个同名 mask。对每个支撑在 clippedDomain 的有限集合 S，`recenter_clippedConfig` 证明完整配置等于 `state S`，包括所有外部格点。

原更新侧还实际证明了更强的动态连接：`update_recenterConfig` 与 `rawStep_clippedConfig` 接已有 `SquareSpin.rule`／`cellUpdate`；`finiteMaskedRawStep` 在真实 finite mask 外恒等，内部调用原 cellUpdate。`rawWord_clippedConfig` 将同一有限 vertex 事件列表逐点 recenter，保留每个 `e.2` tie，并借每步支撑保持证明整个 raw 有限字的等式。

**改造侧仍只给出终态的有限配置表示。** `modified_clippedWord_finite_representation` 没有证明 finite cleanup 与无限格 cleanup 的动态共轭，也没有随机 clock 或 marks 的 law、停止时间 law。原更新侧的确定性共轭同样不自动给出这些随机结论。

## 不可扩张的结论边界

- `L²/1600` 是方块内格点数下界，不是“首个退出前已经删除的面积”。后者还需 Good 轮廓、退出点定位及实际历史。
- 2-core稳定不保证连通、无孔或单一简单轮廓，也不保证 CMST 周长关系。初态稳定和每步稳定不能替代 Good 不变性。
- 本阶段两个 word 都未引入停止规则。未停止 word 的同事件支配不能无条件延伸为“改造链停止后对原链的全部时刻支配”；必须另证目标失败事件与首退出时间的正确包含。
- 固定的任意有限事件字不等于独立 rate-one Poisson 时钟产生的随机字，也不证明有效翻转率、生成元或物理时间的概率估计。
- 完整 `τ(N)=Θ(N²)`、CMST/FSS 核心上下尾、一般扩展期望有限及最终常数均未由本阶段得到。

## 本阶段冻结源

| 模块 | 公开定理 | SHA256 |
| --- | --- | --- |
| `ClippedDiamondGeometry.lean` | 24 | `8c092c3463aa7a736806f593028fa9eaeb9930fbfcb6fffd8979163b87baa1ef` |
| `DropletModifiedWord.lean` | 33 | `3cf40bef3bb6e11da17d9b7d1806b2c77ce5e68acf16a81879cad5fa0f6f9a37` |
| `ClippedSquareCoordinates.lean` | 22 | `c6cd6a6745efd54a81db2dcb0180db52614e316b6e86f36595324a7bf7f65376` |

## 最终统一证据及独立复核

主代理实际统一验收记录为 `2026-10-16T13:32:26.845324+08:00`。本代理于北京时间 `2026-10-16T13:33:40.415111+08:00` 独立重算并核对 [clipped-droplet-independent-evidence.json](clipped-droplet-independent-evidence.json)，证据文件 SHA256 为 `fb2d2b7a6efcff3588235d0cc6cd1368b8caa2ce0360e45c0409a39868521c28`。

| 项目 | 独立复核结果 |
| --- | --- |
| 分析实际范围 | 101个证明模块、1333条公开定理、102份正式源码；实际路径集合与验收记录完全一致，全部源 SHA256 匹配 |
| 实际构建和内核审计 | 统一构建日志正常成功且退出0；`lake env lean --trust=0 AnalysisAxioms.lean` 审计退出0；1333个互异公开声明均有实际公理输出，与源码声明及审计指令集合完全一致；未遗漏名称中合法撇号 |
| 当前分析工具链 | Lean 4.35.0-rc4；记录的 mathlib 为 `54c01c3314d33d15d77893cbe4e0472ff26bb34d`；当前构建警告为空 |
| 核心工程 | 8份源码与既有成功验收的全部散列相同；125条定理及1个模型定义共126条公理输出完整匹配，保留独立 Lean 4.35.0 工具链的构建及 `--trust=0` 记录 |
| 全源与实际输出 | 总计110份正式源码及1459条受审计声明（其中1458条为定理，另1条为核心模型定义）；逐文件散列、每声明公理集合和日志散列均写入独立 JSON |
| 传递公理 | 分析和核心都仅出现 `Classical.choice`、`Quot.sound`、`propext`；没有 `sorryAx` 或自定义公理 |
| 与上一阶段比较 | `history/2026-10-15-2317/analysis-validation.json` 的98个原证明模块散列全部未变；仅统一导入入口改变，另增本阶段3模块79条定理，无删除源 |
| 文本排查 | 对全部110份正式源码去注释扫描，未发现 `sorry`、`admit`、自定义 `axiom`、`unsafe`、`native_decide`、`implemented_by` 或 `debug.skipKernelTC` |

本代理未修改任何 Lean 源码，未重复启动构建，只读取主代理真实构建和标准内核审计日志后独立核对当前文件。文本扫描本身不代替内核验证；本审阅也不构成工具链供应链认证、人类专家签署或完整主定理验收。阶段验收关闭的是上文列明的确定性剪角几何与有限字连接，未关闭的概率、轮廓及停止义务保持明确。

