# 保护域角点、真实停止轨迹与已删面积：2026-10-18

分析142个证明模块、1953条公开定理、143份分析源；核心125条定理及1模型、8份源未变；合计151份正式源、2078条辅助定理。本轮新增6模块62条定理、65个命名声明。统一构建与标准Lean --trust=0审计成功（2026-10-18T23:29:46.112117+08:00），仅Classical.choice、Quot.sound、propext；无占位或自定义公理。

四个保护演化模块先独立统一验收1940条分析定理；随后空象限/退出面积两模块升级到1953条。52项和13项逐声明审计均成功，新源码无Lean警告，保留既有batteries本地修改提示。全部旧136分析证明模块与8核心源保持指纹。独立AI复核不等于人类专家认证。

## 实质成果

- ProtectedColumnGeometry：实际内菱形D⊆S⊆剪角域C、行列凸、Stable和占据degree2，排除水平及垂直对置细颈（L≥2）；erase和cleanup保持行列凸。
- ProtectedCornerGeometry：相邻两方向占据、另两方向空的角点，其共同对角格也占据；四向均已证。只需真实D/C与行列凸，不需预先假定Stable或FourConnected。
- ProtectedDeathConnectivity：将局部二边旁路通过路径投影升为全局连接；保护条件下真实degree2死亡并cleanup保持四邻连通及行列凸。
- ProtectedEvolution：实际modifiedStep和modifiedTrajectory在保护集首次失守前，且包括失守那一步，保持行列凸、实际四连通、cleanup稳定和C支持；真实stoppedTrajectory所有事件索引都保持这些性质及NoCheckerboard。∞不被错误当作零；Shape只是四个离散性质，不是GeometricGood。
- OrthogonalVacantQuadrant：一般有限行列凸且实际四连通集合，任意空点至少有一个完整strict坐标象限不相交。包含空行/列、空集情形；无保护域或概率输入。
- ProtectedExitArea：真实保护集失守时，从空象限选实际directedBlock，使其全落C\S，故L≥40时当前净缺失面积至少L²/1600。实际stopped过程exit≤n后，初态card−当前card至少该量。它不意味着未冻结面积单调，也不是累计raw死亡/额外cleanup总数。

## 证据和边界

[统一构建和公理](audit/analysis-validation.json)、[保护阶段声明](audit/protected-stage-declarations-validation.json)、[面积阶段声明](audit/exit-area-stage-declarations-validation.json)、[保护阶段独立审阅](audit/protected-stage-semantic-review.md)、[面积阶段独立审阅](audit/exit-area-stage-semantic-review.md)、[方法账本](../research/followup/METHOD_LEDGER_2026-10-18.md)。

原模型、真实law、∞、原尺寸和exact-N量词保持。当前尚未证明一般GeometricGood与离散性质等价、原连续frontier/弧长不变量、实际物理停止law/生成元及CMST/FSS自含核心尾与最终二次主定理。完整目标未完成。

Gauss–Bonnet常漂移的直接简化尝试被mask边界反例挡住：全格点角差4不能当成clip内部角差4；域外被禁止的出生改变真实生成元。该候选不能拿来代替核心概率论证，详情见方法账本。
