# 可复用方法账本（2026-10-21）

响应用户授权，由独立AI代理`/root/history_audit_1021`接续记录。方法来自当前实际Lean阶段；这是内部方法整理与语义核对，不认证新颖性、文献优先权或人类专家审查，也不宣称完整主定理已证明。

## 从固定时刻可测到随机退出点可测，补的是乘积历史

上一阶段已构造真正F_t可测的冻结状态代表，并在同一真实概率一集合∀real t识别原stateAt。共同全时相等允许在样本自己的exit.toReal处作路径等式替换；但它本身不证明随机取值函数可测。当前ObservedProgressive直接在Iic(T)×Sample的时间Borel×F_T乘积σ代数中重做完整history fiber和唯一状态graph，取得逐样本IsProgressive，再给净缺失面积Real值StronglyProgressive。

此路线不依赖“几乎处处右连续所以大概可测”，也不把坏样本上的旧global-Good回退偷偷塞进自然历史。它为后续可选停止或补偿所需的准确随机时刻接口提供可复用构造。

## 截断观测在截止端点必须另带“已经发生”事件

对s≤T，正确恒等式是arrival≤s iff arrival≤T且min(arrival,T)≤s。后一比较单独使用在s=T时会把所有未来到时误作已经发生。当前Lean源码明确保留arrival≤T，marked版本同时只用截止T已揭示mark=b。

有限字的顺序在s和T之间可互换，也仅因为完整coverage先说明字里每个identity已到s；不能无条件将censored(s)排序替换成censored(T)。这两个端点/前提检查可用于一般带标记离散事件系统的progressive形式化。

## 从可数唯一graph到渐进状态，不调用抽象可测选择

固定时刻的singleton fiber公式完整保留“无graph且初态S=T”的fallback。将这个公式搬到受限时间×样本空间，每个graph仍是可数finite-history fiber并，所以整状态progressive。选择函数的可测性来自精确fiber公式，不来自Classical.choose看似只读过去的直觉。

进一步对离散Finset状态上的Real净缺失面积做observable复合，得到StronglyProgressive；实际F≤F₊关系只用于可测空间单调运输，没有声称F=F₊或未来独立性会自动运输。

## 无穷停时与有限退出面积必须分别给含义

mathlib stoppedValue对τ=∞通过untopA选某任意有限时刻；这足以定义全样本可测随机变量，却不是“无穷退出时面积”的物理解释。当前exitArea在真实停时σ代数中可测，同时只在明确hfin:τ≠∞前提下识别为actual τ.toReal处面积并应用L²/1600界。∞停时本身保留，不因定义一个有界面积observable就宣称τ有限或其期望有限。

ObservedProgressive已正式冻结14theorem/16named，2026-10-20T19:43:11专项build及standardtrust0全部成功，独立逐字节/逐声明证据已核。当前写入时最终全局统一仍待根代理，不与旧2199/161分析源证据混合。见[渐进可测独立报告](../../formal/audit/observed-progressive-independent-review.md)与[证据](../../formal/audit/observed-progressive-independent-evidence.json)。

## 边界修正的正号：掩膜禁止出生会增加净缺失面积率

新MaskedAreaGenerator目前为正在收尾草稿，尚不计正式验收。其准确代数方向值得保留：S⊆D⊆E时，E\D的所有点当前为空；扩展掩膜E允许的出生为净缺失面积贡献负率，而D把这部分禁止。因此rawAreaRate(D,S)=rawAreaRate(E,S)+Σ(E\D) birthIntensity(S,v)，修正非负。

局部强度是degree>2时1、degree=2时1/2、degree<2时0。完整raw率还包括occupied degree<2的确定死亡、occupied degree=2的半速死亡、vacant degree>2的出生及vacant degree=2的半速出生；所有计数明确限制在实际mask。清理额外删除给另一非负cleanupRate；首次失守后冻结生成元为零。

这个分解显示为何不能用全平面角点差4直接声称实际masked漂移恒为2：实际边界禁止的出生会留下额外正项，cleanup预算也不能与它自动抵消。当前只审查确定性有限率代数，尚未证明它是原clock过程的物理补偿、Dynkin公式或二次尾界。

## 后续边界

仍需实际率一clock/fairmark过程的生成元和补偿、适当历史下的停时后future接口、自含CMST/FSS核心概率、重启及原量词最终τ(N)=Θ(N²)。定理数量不是完成百分比，专项通过不是完整主定理证明。


## 待证明路线：吸收坏过去，争取原F下的停时

根代理提出两条新路线，以下只是经源码定义核对后认为数学上可行的思路，尚未实现或验收Lean。

实际eventTime是chronologicalArrival，即每site的sum max(gap,0)，所以全样本按arrival index单调。有限site下，固定t之后若某site有未来到时，Nat最小future-index的到时严格大于t；该site所有future到时都不早于它。有限多个site可取最小正gap，没有未来到时的site给任意正gap。因此全样本都可望取得无新事件的右gap，不需未来局部有限Good(t+1)。这一点依赖site有限，不能直接扩展到无限site跨site到时聚集。

旧globalGood需全未来无碰时；更自然的坏过去只记录已到集无限，或已到identity中有碰时。坏过去点态持久。若将badpast与合法finite-history永久冻结loss作OR，坏过去触发后吸收，就有机会在所有样本上取得loss单调及右局部常值，再用既有firstLossTime_le_iff证明原F下的真停时，避免将F₊停时后的独立性强行搬回F。

原observedLoss在无合法finite graph时回退实际初态，可能在坏路径上“曾失守后恢复保护”，所以不能直接断言其全样本单调。若以empty状态代表坏过去吸收，任意I=∅时empty仍受保护，应改用独立cemetery flag，或明确只对实际非空保护集连接state-missing；不能忽略这个退化参数。共同真实Good概率一集合仍需用于与原physicalExit的AE law识别。

## 待证明路线：固定marks切片，将已证纯clock残余law扩展到joint历史

固定完整mark样本η，map ω↦(ω,η)把joint历史生成元的已揭示mark条件变成常量，preimage为纯clock到时事件或空。因此joint F停时R的每个Rη可望是纯clock停时，E∈F_R的section也属于其停止σ代数。真实product Fubini将joint AE finite转成AEηAEω finite，逐η调用已证ClockStoppedResidual后积分，可望给单site residual与joint过去的真实factorization，无需新strongMarkov前提。

尚需显式证明联合waiting事件可测；section各自可测不自动足够Fubini。新ENNReal/NNReal停时与旧WithTop Real接口也需保留∞并处理负阈值。该路线不直接适用于F₊停时，也不自动从单site factorization推出多site residual向量联合独立、未来marks fresh或完整strongMarkov。这里只记录可行思路和逻辑边界，不能计为形式化成果。


## 掩膜率与确定时刻joint残余：正式专项已完成

MaskedAreaGenerator现已正式冻结，13theorem/17named，2026-10-21T00:26:35专项build与standardtrust0通过，零新Lean warning。独立代理逐字节核正式SHA、声明表及17项完整输出，准确mask/cleanup/freeze及被禁出生修正语义通过；此前草稿状态由此替代。[独立报告](../../formal/audit/masked-area-generator-independent-review.md)。这仍是确定性有限率代数，不是物理补偿或constant drift=2。

固定marks切片路线已先在确定时刻r≥0实现：MarkedDeterministicResidual正式7theorem/8named，专项build与standardtrust0通过、零新Lean warning，源字节与8项输出已独立核。joint waiting事件先证明ambient可测，再真实product Fubini；每个η使用旧纯clock常量停时残余law。最终给真实单site Exp(1)和原joint F_r独立，不泛称任意joint停时/F₊或多site future独立。[独立报告](../../formal/audit/marked-deterministic-residual-independent-review.md)。

两模块及ObservedProgressive的最终统一全局仍等待根代理实际证据；LocalObservedHistory及原F吸收停时仍仅草稿/路线，不计这些已验收专项。


## 2026-10-21 00:29:49 本轮最终统一验收

ObservedProgressive、MaskedAreaGenerator、MarkedDeterministicResidual合计34条theorem/41named，均已完成实际专项和全局统一build、standard Lean --trust=0公理审计。独立代理逐字节核全部172正式源（164analysis+8core）与实际JSON源集相同，完整2233分析及126核心公理输出与#print清单逐名顺序匹配，只标准三公理或无公理。当前2233分析辅助定理，加125核心辅助定理及1模型，共2359项全局公理输出；核心8源未变，本次未重新编译核心。

此前“仍待统一”的形成状态由此闭合；有限率代数不是物理补偿、确定时刻joint残余不是一般joint停时law、∞stoppedValue不作物理退出解释等语义边界保持。LocalObservedHistory及absorbing原F停时仍为后续草稿，不计本轮验收。见三个独立报告的最终统一绑定。


## 坏过去吸收和一般joint停时残余路线已正式实现

LocalObservedHistory正式21theorem/24named、MarkedStoppedResidual正式8/9，合计29/33，2026-10-21T00:35:04专项build及standardtrust0通过、零新Lean warning，独立源码/输出/语义核对完成，最终统一尚待证据。此前“待证明路线”由此有了真实代码，但不提前报完整主定理。

新exit在原nnHistory是真停时，靠全样本有限site右gap、完整past fiber前缀及absorbing cemeteryflag；共同Good识别原physicalExit、真实law和含∞lintegral。它避免了直接把F₊下停时后独立硬迁移到原F，也没有把I=∅的badflag误作状态缺保护。

一般R可依赖已经揭示的过去marks。fixed-mark切片必须同时运输iSup全历史与E∩{R≤t}，才能落入纯clock停止σ代数；真实联合可测后再Fubini，joint AEfinite仅需AEη AEω。得到原F、非负且AEfinite停时的single-site Exp(1)及其停止σ独立。实际无穷exit本身尚未证明finite，后续需用exit∧T实例，而非把所需核心有限性当输入。见[独立报告](../../formal/audit/local-history-exit-independent-review.md)。


## 先截断真实停时，再调用残余law，避开核心有限性循环

ProtectedExitResidual正式9theorem/10named，ProtectedAreaPotential11/11，20/21专项已实际build与standardtrust0通过、零新Lean warning，独立精确语义、SHA及命名输出已核；最终统一仍待证据。[独立报告](../../formal/audit/protected-probability-independent-review.md)。

R=(min(ENNReal exit,T)).toReal先截断后转换，cap≠∞被点态证明；exit=∞时R=T，不能颠倒操作使其先变0。原RealF停时阈值区分r<0空事件与r≥0的min闭阈值，实际R非负/有限均已证。因此能真正实例化marked停止残余law，不需把尚未证明的原退出finite或finite mean当作输入。它为后续bounded stopping/补偿逼近提供无循环入口。

面积势的正确桥也已实现：真实stoppedWord和可测graph/fallback全样本保mask支持，然后card_sdiff得|D\state|=|D|-|state|。只在当前态及真实两mark更新态的支持下用generator congr与常数shift，修复一般initial S相对缺失面积不能自动替换-card的问题。有界Real面积可积被证明，但不等于恢复时间可积，也不代替物理补偿或N²概率尾。


## 2026-10-21 00:41:11 原F停时与实际截断接口最终统一验收

LocalObservedHistory、MarkedStoppedResidual、ProtectedExitResidual、ProtectedAreaPotential新增49theorem/54named，两个专项33+21及实际统一build、standard Lean --trust=0审计全部通过。独立代理逐字节核176正式源（168analysis+8core）的完整集合和SHA，完整2282分析及126核心公理输出与#print清单逐名顺序匹配，仅三标准公理或无公理。当前2407辅助定理及1模型、2408项全局公理输出；核心8源未变，本次未重编。

原F吸收退出版本、其真实原physicalExit law/∞扩展均值、真正可依赖过去marks的单site停时后残余law、实际exit∧T无循环实例、支持正确mask面积势桥接现都已有代码和统一验收。此前待统一状态据此闭合。仍不把单site残余报成全future fresh marks/多site联合独立或完整strongMarkov；有限率代数不是物理补偿，面积可积不是恢复时间可积。UnrevealedMarkInvariance仍属后续草稿，不在这次2282/176内。
