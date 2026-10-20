# 实际掩膜面积率代数：独立AI语义复核

2026-10-21，代理`/root/history_audit_1021`。只读冻结的正式MaskedAreaGenerator、真实stoppedStep/modifiedStep/cleanup eventLoss定义及所用旧接口；不改Lean、不构建、不认证新颖性或人类专家审查。

## 当前状态

正式源码13条theorem、17个命名项，SHA256 `ca1740226ef45a510afac2e566a2c092b9cc308754d2220880287fb3383fdf91`。**精确数学语义、正式专项及最终统一证据通过（最终绑定见文末）。** 已读[专项JSON](masked-area-generator-stage-declarations-validation.json)、[模块构建](masked-area-generator-stage-declarations-build.log)与[17项完整公理输出](masked-area-generator-stage-declarations-axioms.log)，正式源码SHA与声明表、输出顺序完全一致。专项时间2026-10-21T00:26:35.750802+08:00，build/audit exit0、standard Lean --trust=0，仅标准三公理，零新Lean warning。既有batteries本地文档修改提示保留；不以此冒称本轮全局已验收。

## 率的归一化和冻结规则

frozenGenerator对实际mask D的每个site累加两种真实stoppedStep之fair平均减当前potential，对应每个site率一、每次tie mark fair的有限率代数。它不是把总速率归一成一的离散步链；因此没有除以D.card。对v在D外，旧modifiedStep是恒等，省略这些site与实际mask规则一致。

当I不再包含于当前S时，真实stoppedStep返回S，每个生成元项零；frozenGenerator_of_missing无需假定几何或概率。protected guard成立时，potential f(T)=-|T|的rate分成rawAreaRate+cleanupRate。

这只是从实际更新函数构造并验证的确定性有限率代数，目前未证明该算子就是原clock过程的物理时间条件导数或补偿项，不应提前报Dynkin或martingale。

## raw/cleanup精确面积分解

modifiedStep_subset_maskedRawStep给出清理后集合包含于raw后集合，因而旧eventLoss的Nat减法是准确非负基数差，不是被截零掩盖负号。modified_card_diff先用该subset支持Nat.cast_sub，再把原card到modified card之差拆成raw card变化和真实extra cleanup删除，符号正确。

raw_card_diff对当前occupied/vacant及localRule false/true的四种情况准确给+1、0或-1。raw_local_rate再使用实际无中心四邻majority4和同一identity fair mark：occupied degree<2贡献1，occupied degree=2贡献1/2；vacant degree>2贡献-1，vacant degree=2贡献-1/2，其余零。此处保留出生的负贡献，没有把当前净面积缺失误作累计死亡。

rawAreaRate_counts把四类精确限制在D内，而不是全平面总角点。cleanupRate为额外删除的fair平均，点态非负；无需把清理预算当作出生边界修正。

## 被禁止出生的mask修正符号

rawAreaRate_mask_correction明确要求S⊆D⊆E。对v∈E\D，hSD强制v不在S，因此该site的raw净缺失面积率恰为-birthIntensity(S,v)。按有限和sdiff分解，得到rawAreaRate(D,S)=rawAreaRate(E,S)+Σ(E\D)birthIntensity(S,v)。birthIntensity非负，故扩大mask会使该净缺失面积raw率不增。

这个正号很重要：禁止边界出生留下额外正净缺失面积率，不能从全平面角点差直接得到actual masked恒漂移2。公式不要求几何Shape，条件更稳健；但若当前占据集合不含于小mask D，outside修正可能含死亡，不能删除hSD。

## 接到真实缺失面积前的额外桥

本模块potential为-|current|。ObservedProgressive面积为|initial S\current|，在一般initial S⊆D时不自动与前者只差常量，因为过程可能在D\initial S出生。对本项目实际initial S=D且状态始终含于D时，才有|D\current|=|D|-|current|；之后通过生成元常数不变性桥接。本报告未把这段后续接口冒称已证明。

## 未完成边界

尚缺原actual rate-one clock/fair-mark law到此算子的真实补偿/条件导数、适当历史下停时后future接口、正确几何/边界估计、自含CMST/FSS核心概率尾及原τ(N)=Θ(N²)。独立AI与局部内核成功不等于人类专家认证或完整主定理。


## 最终统一验收绑定（2026-10-21）

实际统一时间2026-10-21T00:29:49.375013+08:00：分析2233条辅助定理/164分析源，build_exit=axiom_audit_exit=0、kernel_trust_level=0。独立代理逐字节核全部164分析源和8既有核心源，共172正式源，源集与各JSON精确一致；本模块正式SHA同时匹配专项和全局JSON。全分析2233项、核心126项完整公理输出与各自#print清单顺序逐一相同，含带撇号声明名；只标准三公理或无公理，无占位公理。core8源未变，本次没有由审查代理重新编译核心。

新增ObservedProgressive14/16、MaskedAreaGenerator13/17、MarkedDeterministicResidual7/8，合计34theorem/41named，各专项均build/audit0、standardtrust0、零新Lean warning。当前合计2358辅助定理及1模型、2359项全局公理输出；既有batteries文档本地修改warning保留。本轮没有重新语义审阅所有旧定理，当前独立复核限于本报告精确新阶段及所用接口。

因此前文写入时的“等待统一”是历史形成状态，现已由实际证据闭合。仍在草稿的LocalObservedHistory不在本次2233/172验收中；完整主定理、后续概率与补偿缺口未因统一成功消失。独立AI不等于人类专家认证。
