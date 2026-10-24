# 加权面积的实际公式、立方门槛和NW配对

完整原同步τ(N)=Θ(N²)定理仍未完成。本阶段不把原clock物理时间等同同步轮数，不假设恢复/退出有限。

WeightedExitArea实际证明：L≥80时，首次失保护后冻结状态的加权缺失W至少L³/128000。依据真实空象限的小块至少L²/6400点，每点权重w=L+2−norm1至少L/20；事件已连接真实原clock law，保留∞。

WeightedAreaDynkin实际证明：先将任意有限mask可观测量f(U∩D)用显式powerset范数和界住，进而真实strict-before状态、signed事件求和/可积与predictable补偿给物理Dynkin。具体加权missing实例有∀U的截取不变式，所以最终结论是真实W，而非替代截取过程。另真实weighted cleanup累计≤(L+2)(4L+2)，清理可一次删除多点，全部计入，没有额外补偿/目标矩界参数。

WeightedAreaTail实际有限代数给加权生成元=冻结expanded weighted raw+cleanup；域外可能出生都在零权层，普通面积修正没有消失。先证明样本/时间均值可积，再得到E[W_T]≤expanded raw真实积分+(L+2)(4L+2)，以及P(exit≤T)≤E[W_T]/(L³/128000)。末条继承原CLOCK灭绝CDF界，不是同步界。

WeightedRawContour实际证明NW角与前列端点后的出生谷注入配对，权重差由真实west暴露边段支付，所有付费边段互不重叠，最多一个未配角。因此真实northwestCharge≤L+2+perimeter；没有匹配或turn-count假设。WeightedReflection实际邻居bijection给degree/Stable/Shape/perimeter及weighted raw反射不变，实际centered square必须L≥1。

2026-10-25T05:01:12.384960+08:00统一：2775分析theorem/207分析源，核心125theorem+1model/8源沿用原验收且hash未变，共215正式源/2901完整公理输出。真实统一build0/标准Lean --trust=0审计0，18+56+53+15共142新named专项均0，仅Classical.choice/Quot.sound/propext，零新Lean warning。5模块122新theorem。完整原source/table/log/入口保存在audit/history/before-weighted-raw-bound-2026-10-25/。

[独立语义审查](audit/weighted-area-independent-review.md)只覆盖审查者未写的三个加权模块；[最终绑定](audit/weighted-area-independent-final-binding-evidence.json)独立核全部215源/2901实输出。AI不是人类专家，未宣称每份模块都另有人类专家认证。

下一阶段为WeightedRawRate的四方向真实局部分类/汇总，争取weighted raw≤18L+12；PhysicalWeightedDrift再接actual beforeShape与积分，争取在真实T=cL²、L≥明确门槛时exitCDF≤1/2。当前这两个文件仍是draft；原同步时间比较、exact-N下界与上界核心尚待，不把这些结论作为最终参数。
