# 保护几何与真实改造轨迹：独立语义审阅

审阅者：`/root/method_ledger`，独立 AI 只读源码与证据核对。未修改 Lean、未启动重复构建；本报告不构成人类专家认证。日期及冻结源指纹见[机器可读证据](protected-stage-independent-evidence.json)。

## 结论与验收边界

四个冻结模块的52个命名声明与源码、标准 `--trust=0` 公理输出完全对应，四份源码 SHA256 均匹配命名审计记录，构建/公理审计记录退出0；独立解析只发现 `Classical.choice`、`Quot.sound`、`propext`，未发现 `sorryAx`、错误或新不可信构造。本次新增49条定理、3个定义，未把定义混算为定理。旧136份分析证明模块及8份核心源指纹保持，仅分析入口加入四模块。

全局统一验收已于2026-10-18T23:19:59.785575+08:00成功，审阅者随后独立核对全部141份分析源、8份核心源指纹与正式源集合；从实际分析源独立提取1940个定理名，与全局1940项公理输出完全一致。核心沿用125定理+1模型的成功记录，并核对当前8源未变及126项打印输入/输出完整一致。共149份正式源、2065条辅助定理、2066项全局公理输出；mathlib当前HEAD与固定提交一致。所有新草稿排除在正式计数外。仅保留既有batteries本地修改提示，无新增Lean源码警告。

## 逐模块数学复核

**ProtectedColumnGeometry。** 实际 `innerDiamond L⊆S⊆clippedDomain L`、行列凸、Stable、v占据且degree=2、L≥2，排除东西及南北同时占据。正负外向支通过真实轴点和区间凸成为同一行，有限最外点degree≤1与Stable矛盾；坐标交换运输实际集合、degree和Stable，不是形式上改名。由无对置邻居得到erase后的行列凸，再接真实cleanup保凸。该模块本身不宣称连通或原始Good。

**ProtectedCornerGeometry。** 东北定理只需实际保护/剪角包含、行列凸、v/N/E占据而W/S空；无Stable/FourConnected假设。内D轴见证产生四个严格不等式，九种符号情形与N/E的clip界矛盾，L≥2余量明确。反射是实际有限集合image，成员等价利用反射自逆；真实D/clip反射保持，方向及空缺条件正确运输，四个对角填充结论作用域一致。没有把单纯角点度数当成一般连通保证。

**ProtectedDeathConnectivity。** `path_erase_of_neighbor_bypass` 对原路径每次经过待删点的片段作真实路径替换：把待删点映到其一个占据邻点；入边、出边接占据邻居间的旁路，其余边直接保留。若没有占据邻点，则借已有degree<2路径删除定理。端点显式要求不等于被删点；升为FourConnected时端点来自erase，得到所需条件；空集合使用既有全称连通约定。

四个角点的占据对角在erase中给两步旁路，实际四邻无自环确保邻居不等于被删点；旁路中间点显式不等于被删点。degree=2枚举与对置排除只留下四个相邻方向，故覆盖全部实际degree2死亡。原FourConnected是输入，经过路径替换得到erase连通，随后接真实legal cleanup连通。`actual_protected_death_preserves` 连接真实mask内、tie=false的modifiedStep，不把cleanup视为恒等，也未声称只删一点或两点。

**ProtectedEvolution。** `Shape S` 精确是行凸、列凸、实际四邻FourConnected、cleanup Stable四个离散性质。它不是`GeometricGood`的新名字，不包含真实frontier简单闭曲线、最小外框周长或Euclidean弧长等条件。

`actual_modifiedStep_shape` 的输入含**更新前**实际innerD包含和clip支持，使用真实modifiedStep的恒等/出生/死亡分类，再由真实cleanup稳定与支持结论收口。输出保Shape与clip支持，**没有输出innerD包含**，所以允许该步正好造成首次保护退出；未把待证明的保护保持偷放进结论。

轨迹归纳只要求各严格前序索引k<n的innerD包含。`exitTime` 检测的是实际 `protectedSites=innerDiamond∪外四邻边界` 首次不再完全占据，可为∞。因此在n≤exit的条件下，严格前序都含innerD，得到**包含退出那一步**的Shape与支持；不推断退出后原未冻结轨迹仍保持。n=0及exit=0也通过原初态Shape处理，不强行要求初态保护包含。

`stoppedTrajectory` 按真实事件索引冻结：有限exit≤n取exit时状态，未退出则取n时状态；∞不会满足∞≤有限n，所以不被toNat误截为0。该结论对任意事件流逐点成立，未建立Poisson物理停时/过滤族/生成元或停止law。初态clip在L≥2满足Shape，故所有冻结端点有Shape，最后由实际行凸+FourConnected推出NoCheckerboard。NoCheckerboard是2×2占据模式条件，不等于完整frontier简单性证明。

## 尚未解决及误读预防

本阶段足以闭合真实degree2角删除及cleanup的离散凸性、占据连通性，并升为真实事件序列的冻结不变量。它并未证明一般原始GeometricGood等价/保持、双删数量上界、物理首退出已删面积、真实停止过程law/生成元、CMST/FSS二次核心尾或完整同步原模型主定理。所有新定理使用的参数均是明确的几何/状态条件，没有把目标概率尾或最终二次结论作为新增假设。

源代码、52项逐声明覆盖和审计来源见[命名验证记录](protected-stage-declarations-validation.json)、[标准内核输出](protected-stage-declarations-axioms.log)、[构建日志](protected-stage-declarations-build.log)。
