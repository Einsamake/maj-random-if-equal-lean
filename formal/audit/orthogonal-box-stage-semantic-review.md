# 一般行列凸周长与真实最小框：独立语义审阅

审阅者 `/root/method_ledger`，只读实际源码与证据，没有Lean源码编辑或重复构建；不是人类专家认证。最新状态及源指纹见[机器可读证据](orthogonal-box-stage-independent-evidence.json)。

两个正式模块的40项命名声明（31定理、9定义）专项build与标准trust0成功已独立核对（2026-10-18T23:49:33+08:00）：两份源码hash匹配、40项源码声明与公理输出完整一致，仅标准三公理，无sorryAx或错误，无新增Lean源码警告。OrthogonalPerimeter为20定理+4定义，OrthogonalPhysicalBox为11定理+5定义。历史draft及日志保留为独立证据范围，不混入正式计数。全局统一也于2026-10-18T23:50:31+08:00成功，审阅者独立核全部145份分析源及8份核心源的153源集合/指纹、源码1984定理名与1984项分析公理输出完整对应；核心125定理+1模型的126项输入输出覆盖完整，共2109辅助定理、2110全局输出。前面积阶段142个分析证明模块及8核心源均未改，入口只接两个新模块。只有标准三公理，未见新增Lean源码警告，保留既有batteries本地修改提示。前1953面积阶段报告/JSON保留历史快照。

## 周长与投影

northCells/southCells定义的是实际占据格且其北/南邻空的集合。每个占据列总有最高/最低占据点；列凸保证该列只有一个向北/向南暴露格。投影构成真实双射，东西方向经实际坐标转置运输。真实exposed side总数等于四方向格数，给出P(S)=2(cardπxS+cardπyS)。该恒等式只需行凸、列凸，不额外假设连通、稳定、保护域或非空，空集亦可覆盖。

投影连续性是另一接口：实际FourConnected路径跨整数cut强制每个介于两投影值的坐标都出现，不需行列凸。有限非空投影精确等于min/max之间的Icc。连接两接口得到integer spans公式；跨度是max+1−min，对应单位格而不是格点间距，toNat保留非负整数转换。

## 正式最小物理框的作用域核对

对任意非空有限S，box坐标是minX−1/2、maxX+1/2及y对应两端。actual unitRegion是以实际格点为中心的闭单位方块并，故利用占据格坐标界得到region⊆box；有限闭区域的frontier也在box内。

最右占据格东邻不占据，真实暴露边的physicalSource在actual frontier上并恰达到maxX+1/2；其他三方向同理。任何包含整frontier的轴平行闭矩形必须容纳这四个真实极点，故包含box，得到集合包含意义的最小矩形。由frontier⊆closed region也得到region对应最小性。此部分不需行列凸、FourConnected或Stable。

最后perimeter_eq_minimum_rectangle另需行列凸、FourConnected、非空，由真实integer跨度转成Real宽高，得到暴露侧边数等于实际最小矩形的2(width+height)。这里没有把简单边界、Jordan曲线、单一连续参数或Euclidean弧长当作已证；Plane的拓扑frontier不自动提供弧长等式。它只闭合原Good条件中的最小框/周长数值接口。

## 当前边界

两模块40项冻结专项与全局1984项分析定理的统一集成都已独立核验。本轮八模块新增93条定理、105named；辅助数量不表示原主定理完成率。一般GeometricGood连续曲线与弧长、物理停止law/生成元、CMST/FSS概率核心及完整主定理仍未完成。不能用本阶段矩形周长等式替代这些剩余结论。
