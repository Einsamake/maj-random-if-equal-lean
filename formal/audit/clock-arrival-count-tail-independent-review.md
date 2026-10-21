# 实际到时的快速响铃概率界：独立审查

当前：正式模块4条定理、4个命名声明逐原文语义、正式源码SHA与全部专项输出已独立核对。专项实际build0、标准Lean --trust=0审计0，仅标准三公理，零新Lean warning。正式SHA256：`234e071a8a3553b2fcf99172fed9e203b787c4362b76e0ab8861241898daa121`。最终统一于 2026-10-21T20:46:21.454420+08:00 实际build0/标准trust0审计0；本代理逐项核完整183正式源集合及所有SHA、2371分析与126核心的全部2497项公理输出逐名逐序一致（含名称内撇号），并将四新模块50theorem/53named与统一源码绑定。核心沿用旧审计、8源SHA未变，未冒称本轮重编。独立AI检查不是人类专家认证；主定理尚未完成。

## 对读者的意义

已经严格证明：固定一个格点，在同样短的时间里挤进越来越多次响铃，其概率会按次数快速下降。同批MarkedRingIntegrability已将这些概率相加，完成有限平均次数；本模块提供其实际概率界输入。

## 实际数学连接

- 复用的是既有GreedyClockChain.lower_tail，传入a=1和长度k+1的常格点路径。新模块没有输入Poisson计数分布、精确均值、独立计数增量、物理补偿或欲证的可积性。
- constant_chain_le_arrival_ae实际构造index=id的到时witness。实际chronological arrival与raw arrival在同一AE集合相等，所有间隔严格正；由此证明第一响严格晚于0及后续严格递增。零时刻坏路径不被硬当作合法第一strict ring。
- witness给chainTime(k+1)≤arrival(v,k)，所以arrival(v,k)≤t推出chainTime(k+1)≤t。事件包含方向正确，足以把已证chain低尾界传给实际第k+1响。
- k从0编号，最终界为P(arrival(v,k)≤t)≤exp(t)·2^(-(k+1))。保留≤阈值，不把≤偷换成<；实t无须非负，负t情形也在形式定理范围内。
- 从概率measure转measureReal再转回ENNReal，只使用实际概率measure的有限性；这里的by finiteness不是假设响铃计数期望有限。实际∞与AE等价处理由既有clock/chain构造保证。

界不声称精确Poisson law或精确平均次数t；固定时间很大时右侧可以大于1，这是合法但不锐的上界，按k仍可求和。GreedyClockChain旧源SHA与原统一JSON一致，没有改动旧Laplace证明或引入循环。

同批平均次数求和已实际验收，后续仍缺真正原历史下的计数条件增量和物理补偿；更没有闭合CMST/FSS核心消退时间或原二次主定理。本审查不改Lean、不构建。
