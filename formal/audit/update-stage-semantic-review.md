# 真实多数更新、清理和边界预算：独立语义复核

记录时间 2026-10-17T10:32:23.762385+08:00。审阅者 `/root/update_semantic_audit`，独立AI内部审阅，未修改Lean、未重复构建。主定理仍未完成。本报告绑定本阶段冻结源码与root实际构建/标准内核输出，不构成人类专家认证。

## 本阶段语义

未发现以下8模块已验收陈述的未解决语义漏洞。它们连接既有四邻majority4、严格多数cleanup、真实有序event word和同一身份marks的clock endpoint。

| 新模块 | 公开定理 |
|---|---:|
| ConvexLocalUpdate | 16 |
| ConvexBirthUpdate | 18 |
| GridCleanupDeletion | 11 |
| ConvexCleanupUpdate | 8 |
| CleanupConnectivity | 6 |
| GridPerimeterUpdate | 13 |
| GridPerimeterDynamics | 16 |
| ClippedPerimeterBudget | 5 |
| 合计 | 93 |

ConvexLocalUpdate将8条草稿正式接入并扩为16条：真实空位degree≤2及出生判据、稳定占据点死亡判据、raw/modified三分分类和真实card变化。RowConvex/ColumnConvex/Stable保留为明确局部前提，未改称一般GeometricGood已证推论。

ConvexBirthUpdate在空位出生时证明有横纵各一真实占据邻；整数区间插入保行列凸，旧degree不降、新degree≥2，故实际cleanup恒等。真实occupied path接入给四连通，坐标投影不变给bbox不扩大。结论只覆盖出生一支。

GridCleanupDeletion的degree损失式同时检查被删点原成员关系。单删稳定/cleanup固定点的充要条件显式保留实际邻点原degree≥3。双删显式保留邻点u原degree2、邻接、成员关系及所有剩余点的双indicator degree预算；先证u删除合法，再用真实稳定终态唯一性识别cleanup。没有把这些局部预算说成原Good自动提供，也未声称每次cleanup至多删两点。

ConvexCleanupUpdate先以no-opposites证明erase保行/列凸。degree<2的实际合法清理步自动满足该测试，沿真实cleanup_reachable链保凸。actual_death_cleanup_convex仍显式保留横纵no-opposites，未从degree2和Stable偷推出它们；未声称四连通保持。

CleanupConnectivity只覆盖degree<2合法删除。实际占据邻域落在某singleton，把被删点投影过去使触及它的path step收缩成零步，其余真实步保留。最终端点是survivors，RTG反身项允许无membership未造成域外绕路。沿真实删除链得cleanup保四连通，包括空集约定；未扩成一般degree2热浴死亡。

GridPerimeterUpdate直接计数每条实际暴露单位facet。插入加法式为P(insert v S)+2degree(S,v)=P(S)+4，删除为P(erase v S)+4=P(S)+2degree(S,v)。不存在Nat截断减法偷换；degree2 raw翻转保周长，但不表示连续边界仍简单。

GridPerimeterDynamics证明真实majority写入对任意S都不增P：写true时degree≥2、写false时degree≤2。域外更新恒等，每个合法cleanup删除至少耗2周长预算。eventLoss由masked raw与实际modified结果card之差定义，cleanup包含关系确保该Nat差精确；wordLoss沿实际演化状态递归累计。结论P(modifiedWord)+2wordLoss≤P(initial)是全程额外cleanup预算，未当作Good、角漂移或恢复时间界。

ClippedPerimeterBudget代入初态真实周长8L+4得到loss≤4L+2。clockOccupied使用ClockEventWord.word z.1 t和既有markedEvents身份marks，word只在旧markedEvents.reverse一次转成时间顺序，没有额外独立marks或重复倒序。clippedConfig(clockOccupied)=DropletClockLaw.endpoint true是既有改造endpoint的定义恒等；未说成原raw endpoint。点态预算对每个时间/sample及旧total-word约定成立，未推导physical stopped-process law、生成元或概率尾。

## 标准内核及完整证据

统一记录2026-10-17T10:28:33.974191+08:00：1891分析公开定理、137分析源，真实build和标准Lean --trust=0公理审计均退出0。独立重算全部137源SHA，集合和JSON完全匹配；源声明、AnalysisAxioms打印请求、1891条实际公理输出覆盖集合完全相同。日志名解析明确支持Lean标识符中的撇号。当前mathlib HEAD仍为54c01c3314d33d15d77893cbe4e0472ff26bb34d。

核心8源指纹与2026-10-14成功记录完全相同；125定理加1模型的126公理输出亦逐项匹配，本阶段未重建核心。合计145正式源、2016辅助定理及2017条全局定理/模型输出。相对05:32保存的1798定理基线，旧128分析proof模块全部未改，仅总入口加imports及新增本轮8模块。新增93定理加5定义/缩写共98命名声明，2026-10-17T10:28:48.069654+08:00专项标准trust0的源、请求、输出和指纹完全一致。

公理仅见Classical.choice、Quot.sound、propext。对145正式源剥注释后检查未见sorry、admit、自定义axiom、unsafe、native_decide、implemented_by或skipKernelTC。新Lean源无warning；保留既有batteries仓库本地修改环境提示。逐源、逐声明及日志SHA详见[独立证据](update-stage-independent-evidence.json)。

## 反例、下一路线及未完成边界

[路线记录](update-stage-route-review.md)保存对置细颈、相邻细颈和小尺度三点清理的明确反例及只读枚举，未冒充Lean定理。本阶段删除接口相应保留必要条件。真实大内域/剪角域排除对置death的数学proof sketch也已独立核对并写入交接，但尚未Lean验收，不计本阶段成果。

对用户早先三个要求：本阶段helper与实际局部规则的连接已核对，标准Kernel输出通过；最终tau(N)=Theta(N²)尚未完成，不能声称其与原主张的完整严格等价已验收；本次是独立AI内部复核，未取得人类专家确认。

仍缺一般GeometricGood等价或足够强离散不变量、大保护几何的raw死亡保持/角点分类、首退出实际已删面积、物理停止law与生成元、自含CMST/FSS核心概率尾和最终常数。当前定理明确的数学条件不是不可信公理，也不能在最终主定理中留作未证明核心输入。
