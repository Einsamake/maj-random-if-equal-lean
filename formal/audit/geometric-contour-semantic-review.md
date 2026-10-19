# 实际区域、连续简单闭轮廓与初态 GeometricGood：独立语义复核

复核日期：2026-10-17（北京时间）。独立证据复算：05:27:43.483074+08:00。审阅者为未编写本阶段 Lean 证明的独立 AI；曾提供原文、几何单位和度量接口建议，没有修改 Lean，也没有重复构建。这不是人类专家认证。

## 验收结论与范围

本阶段通过源码语义和既有真实内核验收记录的独立复核。对实际 clipped 初态及整数 L ≥ 1，已证明原单位占据区域的整个拓扑边界是一条连续简单闭曲线，且其真实欧氏弧长等于实际最小轴平行外接矩形的周长；同时接入真实内菱形包含和严格多数清理稳定性，得到 ClippedInitialContour.initial_geometricGood。

这一结论只覆盖实际初态。一般 Good 与离散不变量的等价、更新与清理后的 Good 保持、角计数和漂移、停时真实过程 law、退出时删去面积、CMST/FSS 二次概率界及最终 τ(N)=Θ(N²) 主定理仍未完成。

## 原文对应与单位

直接核对 [CMST 原文 §8 Definition 7(a–f) 与 Theorem 7 证明](https://arxiv.org/html/1007.3599v2)。原区域由整数格点为中心的边长 1 闭正方形组成，Good 使用整个区域边界、边界坐标极值及几何周长。内菱形包含条件与退出事件所用的内菱形加外邻边界是不同条件。

项目早先采用边长 2、奇整数端点的放大坐标；本阶段用明确的 halfScale 同胚转回原单位。unitRegion 的每个单元是中心 v、坐标 v±1/2 的真实闭正方形。原文审阅和固定 mathlib 接口依据另见 [region-polygon-source-review.md](region-polygon-source-review.md)。

## 逐模块语义核对

| 新模块 | 公开定理 |
|---|---:|
| GridCellRegion | 22 |
| GridRegionBoundary | 18 |
| GridPhysicalRegion | 19 |
| ClippedBoundaryPolygon | 10 |
| ClippedBoundaryCurve | 15 |
| GridContourLength | 6 |
| ClippedRegionBox | 11 |
| ClippedPhysicalBox | 15 |
| ClippedInitialContour | 13 |
| 合计 | 129 |

GridCellRegion 的 region 是实际有限个闭单元的并。紧性、闭性、单元严格内部的唯一归属均从定义证明。暴露边属于占据单元，也属于相邻空单元的闭包，因此整个闭线段（含端点）属于实际 frontier。没有把边界定义成方便使用的抽象轮廓。

GridRegionBoundary 反向分类单元内部、四个相对开边和四角。相邻占据单元覆盖跨边开邻域，四个占据单元覆盖角点开邻域；混合四角状态产生真正占据至空缺的暴露边。因此对任意有限 S，实际 frontier 精确等于所有暴露完整闭线段之并。此恒等式无需预设单圈、无夹点或 Jordan 定理，没有漏掉对角接触情形。

GridPhysicalRegion 明确证明 halfScale 对单元、区域、frontier 和完整线段的像恒等式。单边长度 1 的坐标算式只作尺度核对；最终曲线长度使用独立的真实欧氏 variation 证明。

ClippedBoundaryPolygon 由真实 successor 的完整周期枚举所有实际 facets，与 Fin (8L+4) 双射，并处理循环末端。实际 Polygon.edgePath 等于对应完整仿射 segmentPoint；不同边只能在共同端点相交，非相邻边不交。Polygon 本身只是顶点数据，简单性并未从类型名推出，也未错误要求所有连续三顶点不共线。

ClippedBoundaryCurve 递归拼接实际线段，逐段端点匹配给出连续性；真实周期给出闭合。对半开周期使用整数部分分解与线段内部单射性，并由不同线段只能端点相交、真实 source 顶点单射，证明整条曲线单射。闭区间像覆盖全部 polygon 边界，包括最后端点，不只是枚举顶点。

ClippedRegionBox 和 ClippedPhysicalBox 对实际整个 region/frontier 证明外接矩形包含。四个真实 frontier 极值点证明最小性。物理单位跨度均为 2L+1，矩形周长为 8L+4；这一步没有仅凭 facet 数量冒充连续弧长。

GridContourLength 使用真正的 EuclideanSpace ℝ (Fin 2) 的 L² 距离，没有把 ℝ×ℝ 默认的 max 距离当成欧氏距离。逐个物理轴向线段通过平方距离恒等式证明为等距嵌入，再从 eVariationOn 对所有单调有限分割取上确界的定义得到区间长度；最后对真实 trace 的所有闭单位区间用 variation 可加性求和为 8L+4。结论保留 ENNReal，没有通过有限抽样或提前转实数掩盖无穷情形。

ClippedInitialContour 将 polygon 边界与实际 region frontier 恒等式、halfScale 的 frontier 像、闭合单射曲线和真实欧氏长度组合。physicalTrace 已经缩放，euclideanPoint 不再除以 2；其复合与前述 unitTrace 定义相等，避免重复缩放。弧长计算在 physicalTrace 的参数区间 [0,8L+4]，与其遍历整个 frontier 的周期一致。另有 [0,1] 归一化曲线证书，未将两个参数区间混用。

最终 GeometricGood 明确包括 S⊆clippedDomain、innerDiamond⊆S、实际 cleanup S=S、实际 frontier 最小外接矩形，以及存在正周期、连续闭合、半开周期单射且像为全部 frontier 的曲线，曲线欧氏 extended variation 等于该矩形周长。最终定理以实际 clippedDomain 为 S，全部字段由已证明事实组装。审阅提出的 ambient domain 包含及 frontier 最小矩形两项已落实到最终冻结源码。没有将 Good 保持、角计数、漂移或核心概率界塞入定义或作为本定理假设。

## 构建、公理与完整集合核对

分析工程统一验证时间为 2026-10-17T05:25:26.419192+08:00。真实构建和标准 Lean --trust=0 公理审计退出码均为 0。独立复算 129 个分析源的全部指纹和 1798 条公开定理集合，逐项匹配源声明、审计源 #print axioms、实际输出及验证 JSON。核心沿用已通过的固定验收，8 源指纹未变，125 定理加 1 个模型定义，共 126 条公理输出亦完整核对。本轮没有声称重新构建核心。

合计 137 个正式源、1924 条全局公理输出。相对 05:09 保存的 1669 定理基线，旧 119 个分析证明模块全部未改，只更新总入口并新增上述 9 个模块。新增 129 条公开定理；另外独立复算新模块 158 个全部命名声明（定理、定义、缩写）的真实专项审计，集合、源指纹、输出和 05:25:46.858240+08:00 的专项记录完全一致，退出码和 trust level 均为 0。

全部实际输出仅出现标准 Classical.choice、Quot.sound、propext，无 sorryAx 或自定义公理。正式源注释剥离后也检查了 sorry/admit/axiom/unsafe/native_decide/implemented_by/skipKernelTC 等禁用构造。新增 Lean 源无 warning；保留环境提示 batteries: repository has local changes，没有将它误报为证明失败或完全无警告。

完整逐源指纹、逐声明公理依赖及日志指纹保存在 [geometric-contour-independent-evidence.json](geometric-contour-independent-evidence.json)。对应真实记录是 [analysis-validation.json](analysis-validation.json) 与 [region-contour-declarations-validation.json](region-contour-declarations-validation.json)。独立检查没有启动额外 Lean 构建。

## 未完成边界

目前是实际初态几何证书，不能据此声称任意状态的离散 Good 等价或真实过程始终 Good。需要继续证明更新和清理保持、山谷与角计数、退出面积、真正停时后的过程 law/生成元及 CMST/FSS 二次尺度概率估计，随后才能完成最终恢复时间主定理。显式 frontier 简单闭曲线证书也没有被扩大为独立 Jordan 分离定理。

未发现本阶段已验收命题的未解决语义漏洞；结论严格限于上述冻结源码与已核验记录。独立 AI 复核不替代人类专家审查，也不构成完整主定理或公开问题已解决的认证。

