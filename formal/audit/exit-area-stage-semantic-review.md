# 空象限与实际保护退出面积：独立语义审阅

审阅者 `/root/method_ledger`，只读复核实际源码、既有定义与证据；未编辑Lean，未启动重复构建；不是人类专家认证。当前13条正式定理已经数学复核，更新后的13项专项审计也已独立核对：两份源指纹完全匹配，实际13个定理名与13项标准内核输出完整一致，build/审计退出0，仅标准三公理，无sorryAx或错误。全局统一也已于2026-10-18T23:29:46+08:00成功，审阅者独立核对全部143份分析源+8份核心源共151正式源的指纹、1953个实际分析定理名与1953项输出完整一致，核心125定理+1模型的126项打印输入输出覆盖完整。共2078辅助定理、2079全局公理输出，仅标准三公理。旧140份分析证明源及8core均未改，分析入口仅接两模块；无新增Lean源码警告，保留既有batteries本地修改提示。前四模块1940阶段的报告/JSON作为成功快照保留，不改写成新阶段证据。指纹、核对时间及机器可读状态见[独立证据](exit-area-stage-independent-evidence.json)。

## 数学作用域

`OrthogonalVacantQuadrant.exists_empty_quadrant` 对任意有限S，只要求行凸、列凸、实际四邻FourConnected及v不占据，就得到经过坐标反射表示的一个**完整严格象限**与S不交。无实际保护域或Stable假设，没有把“已存在空象限”放作参数。

若v所在行列各有占据点，行列凸与v空使这些轴见证都位于对应单侧；反射把见证统一变成右侧和上侧。于是v左侧的水平射线和下侧的竖直射线皆空。假若西南象限仍有占据点，则从它到右侧见证点的真实占据四邻路径无法越过这两条空射线：每一实际四邻步都保留西南严格不等式，最终却应到达v所在行，矛盾。

若某行/列没有见证，连通路径跨对应整数cut会强制在该空行/列出现占据点，故整个集合只能在一侧；选反向严格象限即可。空集由全称FourConnected约定自然覆盖，没有偷偷假设集合非空。反射、坐标交换和cut均运输实际neighbors4与真实Path，不是任意抽象邻接。

`ProtectedExitArea.exists_vacant_directedBlock` 从任意实际protectedSites中的空点出发，用上述strict空象限的反号方向构造真实directedBlock；偏移量是1到L/20，故不落在轴上。已有actual protectedSites=D∪外四邻边界的四向block控制保证该块确实在clip内，空象限保证与S不交，得到真实包含 `block⊆clip\S`。此结论并不假设整个S已在clip内；它只需要区域内存在这样的空块。

面积定理据真实卡数单调性与已有block_card=(L/20)^2、L≥40的整数余量，给出 `(L:Real)^2/1600≤card(clip\S)`；没有将floor(L/20)误当L/20。

## 真实退出接口

`actual_stopped_exit_quadratic_vacant_area` 取真实stoppedTrajectory的Shape，从中使用行列凸和FourConnected；冻结定义在有限exit之后保留退出那一步实际状态，该状态确有actual protectedSites空点。因此结论是实际冻结轨迹的缺失面积下界，而非仅证明域内能摆下一个大方块。

新增 `actual_stopped_area_after_exit` 用 `exit≤有限n` 排除exit=∞，才把exit.toNat转回真实有限索引；不把∞强制看成0。`actual_stopped_area_card_decrease` 再使用真实stoppedTrajectory⊆clip，将 `card(clip\S)` 精确改写为 `card clip−card S`，以Real中的差给出初态到当前状态的净面积减少。

这是事件索引上、已经发生退出时的确定性结论；不是Poisson物理停止law、退出概率或二次时间尾界。净缺失面积不是累计raw死亡数、额外cleanup数，也不意味着未冻结过程的面积单调。出生仍可能发生。所有∞、严格象限和L≥40量词均保留。

## 结论及未闭合部分

未发现这些准确陈述的数学作用域漏洞。前一阶段已证Shape到退出/冻结轨迹接口真实使用，没有把一般GeometricGood或待证明概率尾界当作输入。当前成果把“保护点空缺”接到“实际初态净减少二次面积”；一般Good曲线不变性、物理停止过程、生成元、CMST/FSS核心概率尾与原同步主定理仍需证明。

验收证据：[专项声明记录](exit-area-stage-declarations-validation.json)、[标准内核输出](exit-area-stage-declarations-axioms.log)、[构建日志](exit-area-stage-declarations-build.log)。专项13项及全局1953分析定理的源集合、指纹和全部输出覆盖均已独立确认。该结论不等于完整主定理验收。
