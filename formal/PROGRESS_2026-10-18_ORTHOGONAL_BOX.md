# 一般正交凸周长与真实最小矩形

分析144个证明模块、1984条定理、145份分析源；核心125条定理及1模型、8源未变；共153份正式源、2109条辅助定理。本轮8个新模块93条定理、105个命名声明均经真实构建和标准Lean --trust=0核验。最新统一验收2026-10-18T23:50:31.611929+08:00，仅标准三公理，无新增Lean源码警告。

这是保护停止轨迹/退出面积之后的独立阶段，新增2模块31条定理和9个定义，40个命名声明单独构建、公理审计均退出0。旧142个证明模块及核心8源保持hash，入口只添加两个imports；本机batteries修改仅docs/README.md，未改库证明。

## 已证明

OrthogonalPerimeter：对任意有限行列凸集合S，真实暴露单位格边周长P=2(占据列数+占据行数)。每个非空列有唯一最上、最下暴露格，利用实际有限max/min给出存在、利用列区间凸给出唯一；东西方向由真实坐标交换运输。额外的FourConnected使两个坐标投影都无缺口，非空时精确等于min/max整数Icc，保留单位格宽所需的+1。

OrthogonalPhysicalBox：任意非空有限S的原单位正方形并、其真实topological frontier，均被min/max坐标加减1/2给出的矩形包含，且这个矩形对两者都最小。四个极值由真实暴露格边的physicalSource在frontier上达到。仅加行列凸和实际四连通，真实单位格边P数值等于这个实际最小矩形周长。

这个结论不是一般Jordan曲线、全边界连续参数化或欧氏全分割弧长定理，不把数值格边计数偷换成弧长。原GeometricGood的一般动态保持尚缺这些连接，初态的全弧长结果此前已通过。

[统一证据](audit/analysis-validation.json)、[40声明专项](audit/orthogonal-box-stage-declarations-validation.json)、[独立语义复核](audit/orthogonal-box-stage-semantic-review.md)、[独立指纹](audit/orthogonal-box-stage-independent-evidence.json)、[方法账本](../research/followup/METHOD_LEDGER_2026-10-18.md)。独立AI不代替人类专家。

前阶段仍见[保护演化与退出净面积](PROGRESS_2026-10-18_PROTECTED_EVOLUTION.md)。真实物理停止law/生成元、CMST/FSS核心概率尾与最终原主定理尚未完成。
