# 可复用方法账本（2026-10-20）

本记录响应用户授权：在推进自含Lean证明时，同时记录有价值的方法。记录人为独立AI代理`/root/history_method_record`；仅作内部可复用方法整理与精确语义核对，不认证数学新颖性、文献优先权或人类专家审查，不以局部成功宣称τ(N)=Θ(N²)已完成。

## 当前已验收起点

MarkedClockFiltration的14条theorem/18named已于2026-10-19T21:21:32专项standardtrust0成功，21:22:08统一成功。当前分析2158定理/158源，加8核心源共166正式源。2026-10-20独立代理只读核了本模块实际字节与两份最终SHA、18个逐声明内核输出及exit0记录，补齐旧报告pending；没有重审所有旧定理。[最终历史审阅](../../formal/audit/marked-clock-filtration-independent-review.md)。

## 方法一：把“全局回退代表”与“历史可见代表”分开

旧clock word为在所有样本上有定义，若某有限时窗局部无限，或整个未来任意两到时碰撞，则回退为空字。真实指数时钟下这些坏路径为零测，模型law正确；但全未来无碰时的判据本身不是当前历史信息。过去相同而未来不同的坏样本可能令旧totalword当前值不同。因此不能从ambient可测或AE正确，直接推出这个特定全样本代表对原history适应。

当前路线不把globalGood塞进history，也不重写旧概率过程来消除差异，而是为目标事件重新构造只读过去的可测代表，再在已证共同Good概率一集合上认同它与原过程。这样既保留原law、模型、时间尺度和无穷退出，又精确处理辅助totalization造成的信息边界。

状态：MarkedHistoryWords草稿已形成10theorem/15named，只读语义核对完成，最终正式内核与统一验收待根代理证据。此先导不计入上述验收基线。

## 方法二：截断到时值，再用完整finite history fiber重建执行

数值观察`min(arrival(e),t)`只包含当前之前信息。它的Iic原像分两种：x≥t时全空间，x<t时恰arrival(e)≤x，因此严格排序可在当前history里证明可测，不必观察未来真实到时。到时=t与未来都可能映到t，但完整coverage另行记录arrival≤t，正好纠正这个边界。

每个finite fiber保留三个部分：全部已到identity恰为l的双向coverage、严格真实先后、到时才揭示的mark向量。identity保留(site,arrival-index)，不把同site的多次更新合并。完整coverage+Nodup+严格排序唯一性把这个list精确认同原reverse chronological word；随后真实recenter与原markedEvents逐项吻合，确定性永久冻结执行器接回实际state。

这个拆法把“过去发生了什么”的可测性与“由这些事件算出什么”的确定性递归分开，避免在每次自旋依赖的loss后重新假设独立marks。索引finite list上的Bool向量、Event的可数性保证所有fiber的并确实可数。

## 方法三：只为要用的事件构造代表，先避免不必要的随机变量选择

`observedLoss`对所有finite list与finite mark向量取可数并，只保留其确定性stoppedWord缺I的fiber。每个fiber可测，执行结果对该fiber索引是常量，因此直接得到当前history可测事件；无需先挑一个可测排序列表、处理空fiber选择或建立整个状态函数的全样本适应。

Good路径下双向精确相等足以服务下一停时阈值接口；坏样本上的representative允许和旧global-fallback totalword不同。这是目标导向的可测代表设计，不是借零集跳过证明。实际AE证据、history completion以及原physicalExit阈值运输仍要逐项完成；只得到事件representative不能自动报IsStoppingTime或生成元。

## 继续时必须保留的边界

当前已验收真实联合history本身未偷看未来marks，单ring停时已证。新先导给真实loss的可测代表，后续须接实际measure下同一概率一集合与准确历史接口；仅“固定t AE等价”不够推出原未完备history可测。根代理随后选择下节的有理首达及右连续化路线，不把ambient null σ代数强行加入当前history。仍缺生成元/补偿、真正自含CMST/FSS核心二次概率尾与最终原模型主定理。既有masked Gauss–Bonnet漂移捷径已被反例否定，不因新增filtration工具恢复该失效路线。

细节及当前SHA见[有限历史独立审阅](../../formal/audit/marked-history-words-independent-review.md)。

## 待实现路线：有理首达与右连续化，避免直接替换未完备事件

根代理2026-10-20拟定义`rationalExit`：对所有q∈ℚ、q≥0且observedLoss(q)成立的ofReal(q)取sInf。此为下一接口路线，当前尚未报Lean或统一验收成功。

关键可测门槛改成strict事件：{rationalExit<t}恰为q<t的observedLoss(q)可数并。每个q事件对原F_q可测，q≤t给原F_t可测；t=0时并空，初态已loss时有理inf仍是0。原loss永久冻结后保持，故在共同Good路径上理性样本首达inf与旧physicalExit相等；有限首达可以是无理数，无需强行找有理q等于首达，只需从上方有理逼近，∞情形由始终无loss保留。

Mathlib实际接口`isStoppingTime_of_measurableSet_lt_of_isRightContinuous`要求τ:Ω→WithTop ι及右连续filtration；取ι=NNReal，WithTop NNReal就是ENNReal。先限制联合Real history到NNReal，再取`Filtration.rightCont`。严格事件原F_t可测通过F≤F₊传入F₊，该通用接口给F₊下真正IsStoppingTime。与原physicalExit的AE等式保持原真实law及无穷值，不需要声称旧global-fallback代表本身对原未完备F点态适应。

必须证明的对应包括：strict阈值的精确双向countable union；NNReal与Real/ENNReal阈值转换；原loss persistence及Good识别下的rationalExit=physicalExit；全t在同一真实概率一集合成立。不能只拿逐固定t概率相同代替随机时刻AE相等，也不能把F₊未经证明写成F。

右连续化确比原F稍强，当前仍未证明两者相等。后续若残余等待或未揭示mark条件独立只在原F建立，不能自动用同一lemma当作F₊独立；需适当极限/条件期望接口或另证正确的信息运输。此边界影响后续strong Markov/补偿，不能仅因IsStoppingTime通过而忽略。当前未声称这些后续概率结果。

### strict阈值是必要边界，不是符号简化

不能把{rationalExit≤t}写成“存在q≤t已经loss”。若首达恰为无理t，有理loss见证可能全部严格大于t，但它们的inf仍等于t。真正成立且可数可见的是strict版本{rationalExit<t}。随后右连续历史把从右逼近的strict事件转成≤事件，从而恢复IsStoppingTime定义要求的闭阈值。这个拆法准确填补inf是否达到及有理见证是否存在的不同边界。

## 有理首达阶段正式代码及专项审计已完成

MarkedHistoryWords与RationalProtectedExit现已冻结，分别10/11条theorem，共21条新定理、29个具名def/theorem。2026-10-20T19:30:35专项模块构建和逐29named standardtrust0公理审计全部exit0、零新Leanwarning。独立代理已逐源码核上述方法和边界，并核实际日志、声明表与两个最终SHA；旧草稿hash已被正式hash替代。全局统一尚待根代理后续证据，当前不提前增加2158分析/166正式源基线。

上述“待实现路线”现在已在正式源码实现：原真实history中strict有理阈值可测，实际F₊下IsStoppingTime，原physicalExit的AE函数相等、真正原推前law和含∞扩展均值相等，以及L≥40/t≥0的原clock消失概率比较。它不再只是数学可行路线，也不是只建立了局部某个t的相同分布。仍未把F₊等同F，也未取得停时后独立、生成元、CMST/FSS尾或完整主定理。详见[正式专项独立报告](../../formal/audit/observed-stopping-independent-review.md)。

## 方法四：从可数唯一图像构造全状态代表，而不调用抽象可测选择

ObservedFrozenProcess正式冻结20theorem/23named；2026-10-20T19:33:48专项build与standardtrust0逐项审计成功，实际SHA、声明表和23输出已独立只读匹配，全局统一尚待根代理证据。它把先前只为loss构造的历史代表升级为完整Finset状态。

先在无Good前提下证明任意两个完整finite fiber具有相同严格排序identity字和相同真实marks，故确定性执行结果唯一。每个T的执行graph是countable finite history并，因此可测；有graph则Classical.choose其唯一T，无合法完整finite history则回退实际初态S。随后通过精确singleton fiber公式证明整个选择函数可测，而不是假定Classical.choice自动保留可测性。

关键公式必须带fallback：state=T当且仅当graph(T)，或所有graph均无见证且S=T。漏掉后一分支会在T=S时出错。Site可数使Finset Site可数，目标采用局部离散top σ代数；不需要可测选择大定理，也不污染全局instance。此方法可复用于由可数有限过去唯一决定、只在坏路径需fallback的递归随机系统。

## 方法五：共同全测集上的过程相等，允许准确搬运随机退出点路径等式

新state对原history和其rightCont均Adapted，且在同一个真实概率一集合∀real t等于原frozen state。这个强于逐固定t AE相等的接口，能够在每条Good样本的随机exit.toReal处准确替换，从而搬运有限退出后永久冻结；toReal始终先有exit≠∞ guard。它还搬运[t,b)右局部常值、0初态、严格退出前原Good和退出后L²/1600真实缺失面积。

这没有把旧global-fallback stateAt冒称原未完备history下适应。共同过程AE相等允许随机时刻的点态代入，却不自动完成该随机取值函数的可测性、联合/渐进可测性或可选停止。后续真实补偿/生成元依然要证明相应接口，停时后独立和CMST/FSS核心也仍缺。[完整状态独立报告](../../formal/audit/observed-frozen-independent-review.md)。

## 2026-10-20 第一完整阶段最终统一验收

19:34:25统一实际build及standardtrust0公理审计全部成功；MarkedHistoryWords、RationalProtectedExit、ObservedFrozenProcess合计新增41条theorem/52named（专项29+23均通过）。最新2199分析定理/161分析源，加8既有核心源为169正式源，2324辅助定理加1模型，2325项全局公理输出。独立代理只读逐字节核全部169源、52新增输出和2199分析+126核心完整输出（含声明名内撇号），只三标准公理，无新增Leanwarning；核心本次未重编但既有8源字节完全匹配原验收。

因此前文“待实现/等待统一”是方法形成时记录，当前上述三模块已经正式验收，不再列其停时代表、真实适应状态、原law/扩展均值或几何运输为未证。尚缺原F与F₊同一性、停时后独立、joint/progressive与随机时刻可测性、实际生成元/补偿及自含CMST/FSS核心概率和最终主定理。根代理新ObservedProgressive草稿正在下一阶段，不在当前169源/41新增定理验收内。

对应[联合停时独立证据](../../formal/audit/observed-stopping-independent-evidence.json)和[完整状态独立证据](../../formal/audit/observed-frozen-independent-evidence.json)。这是独立AI及Lean内核证据，不是人类专家或数学新颖性认证。
