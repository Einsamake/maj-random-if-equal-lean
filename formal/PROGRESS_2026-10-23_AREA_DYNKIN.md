# 真实更新前状态与物理时间面积公式

原同步CA主定理τ(N)=Θ(N²)仍未完成。本阶段处理原clock law下的首次失保护冻结改造过程，不改时间尺度，不假设退出有限。

## 已验收的两个连接

第一批4模块（18:27:15统一）由有理左恒定graph构造原nnHistory标准可预测前态；严格过去真实有限word给出左gap和唯一事件append。单一原样本满概率集上，对所有非负t同时等于真实strict-before状态，包含随机响铃时刻。真实面积单次增量是D-relative的缺失面积增量，正负两部分分别有原事件补偿。201源/2543分析/2669全局公理输出，新增39theorem/46named。

第二批4模块（18:40:51统一）用真finiteword给出路径signed telescope，以有限支撑把原身份事件重索引到Vertex×Bool的真实pathSum；先证明绝对可和、路径和与时间Bochner积分真可积，才交换级数及积分。得到E[A_T−A_0]=Σ_vΣ_b(1/2)∫_(0,T] E[δ_v,b(u)]du，以及单时间积分版本，A_T=card(D\stateAt(T))，初始A_0=card(D\S)保留。205源/2585分析/2711全局公理输出，新增42theorem/45named。没有把全Vertex求和直接称为D上的几何生成元。

两个批次均实际Lake build0、标准Lean --trust=0逐声明审计0，仅Classical.choice/Quot.sound/propext、零新Leanwarning。核心8源沿用旧125theorem+1model验收，仅现场核hash未重编。独立AI语义/全部源SHA/输出名称顺序已核，不是人类专家认证。

## 完整证据

第一批：[独立绑定](audit/observed-pre-state-review-final-binding-evidence.json)，其原JSON/log/table/入口保存在audit/history/before-actual-area-dynkin-2026-10-23/。
第二批：[独立绑定](audit/actual-area-dynkin-independent-final-binding-evidence.json)，其原JSON/log/table/入口保存在audit/history/before-physical-area-generator-2026-10-23/。

## 核心缺口

Vertex补偿量到真实clipped D生成元的连接现已验收（见下节）；仍须控制禁止birth修正的累计影响，完成自含CMST/FSS收缩尾、平方restart和原exact-N最终二次界。masked恒漂移2已被L40实际80反例否定，禁止恢复该捷径或用cleanup预算直接支付被禁birth。

## 最后连接与当前统一

PhysicalAreaGenerator新增10theorem，真实recenter单射及原clippedDomain覆盖已实例化；hL≥1的actual_clipped_area_dynkin无覆盖或补偿结论参数，样本及时间均值真可积。raw+cleanup仍是masked raw，不能代入unmasked常数2。

最终统一2026-10-23T18:47:57.505697+08:00：2595分析/198分析源，核心旧125+1/8仅核hash未重编，共206正式源/2721输出。本轮共9模块91theorem/101named，三组46/45/10均实际标准审计0、三标准公理、零新Leanwarning。最终独立证据见[206源绑定](audit/physical-area-generator-independent-final-binding-evidence.json)。

方向已核：原灭绝CDF≤辅助exitCDF，因此辅助不早exit可给原恢复下界；辅助快exit不能直接给原恢复上界。physical_exit_measure_le_quadratic_area将早exit包含于缺失面积≥L²/1600。下一阶段需要上控平均缺失面积；masked raw的正禁birth修正和正cleanup都不能删掉。
