# 永久首失守冻结与固定物理端点 law：独立 AI 只读复核

核查日期：2026-10-19（北京时间）。代理 `/root/boundary_method_record`。未编辑Lean、未启动Lean构建；审阅不是人类专家认证。读取实际 `DropletStoppedWord.lean`、`DropletStoppedClockLaw.lean`、旧 `DropletDomainComparison`、`DropletClockLaw`、`ClockWordMarks` 与具体 `ProtectedDomainClockComparison` 定义/证明。

## 当前状态

已独立数学语义核查通过，当前两个正式路径中的源码快照和具名声明见[机读证据](stopped-clock-independent-evidence.json)。**最终冻结专项与全局统一验收现已独立逐项核对PASS。** 两模块33条theorem及41个def/theorem/命名instance全部标准trust0；最新2109分析定理、155分析源加8核心源=163正式源，2234辅助定理加1模型，2235项全局公理输出。上阶段2076分析定理/161源保留为历史基线，不重复计数。

## 1. 缺失作为吸收态，避免未冻结过程复活

`stoppedStep D I S e` 当I⊆S才执行真实modifiedStep，否则返回原S；`stoppedWord` 沿实际有限事件字按顺序递归。若初态已经缺I，`stoppedWord_of_missing` 证明任意字均不动。第一次真实modified更新导致失守后，后续每一步都恒等，故当前态一直缺I；未冻结原过程日后恢复I也不能使冻结过程复活。

`stoppedTrajectory_protected_iff` 真正证明“冻结n态含I ↔ n<原modified过程首失守exit”。有限分支先由exit≤有限n证明exit≠top，再使用natCast_toNat连接首失守状态；∞分支不把toNat∞=0当成真实首达。`stoppedTrajectory_eq_of_le` 允许等号，正确保留造成首次失守的那一步实际modified状态；从下一步才冻结。

`stoppedTrajectory_succ` 分当前冻结态是否含I递推：含I意味着n<exit，故n+1≤exit且执行原modifiedStep；缺I意味着exit≤n，两次后续状态均为同一首失守态。initial I缺失时exit=0，从初态冻结；I为空时subset永真，exit=∞，每步均是真实modifiedStep。这些边界不是额外排除条件。

## 2. 全未来首达定义变成有限前缀因果函数

`stoppedWord_prefix_eq` 从实际append递推证明，沿infinite events前n个事件执行有限冻结字，恰等旧 `stoppedTrajectory` 数学定义。有限字用任意fallback补成无限序列后，字长时状态仍相同；有限take k也由实际getD/take等式识别。因此定义中形式上出现的全未来first-hit查询，在时刻n实际只依赖前n个事件。

`stoppedWord_protected_iff` 给出精确历史判定：

> 冻结字终态含I，当且仅当每个0≤k≤字长的原modified前缀态都含I。

其中包含k=0，处理初态缺失；包含k=len，处理最后一步首次失守。`stoppedWord_missing_iff` 是其真实曾失守的存在量词对偶，不把非吸收原modified过程的“当前含I”误作历史存活。

## 3. 固定物理t，真实word/identity marks的推前law

`run` 在给定actual clock identity word上先用旧 `markedEvents` 恰好反序一次变成chronological事件，保留每个identity的原fair mark，再执行新的stoppedWord。`endpoint` 直接代入实际 `ClockEventWord.word z.1 t` 与原mark field z.2；异常样本仍沿旧total-word fallback，未替换真实law。

`freshRun_fixedVector` 用旧同identity的marks恢复等式证明fresh finite vector执行与原mark field执行同态；fixedRun/endpoint measurability均由实际可测函数复合得到。这里原来的clock word选择只依赖时钟，不读取自旋/marks。

`endpoint_joint_measure` 在真实wordFiber与任意额外可测clock event E交集上，通过已经证明的 `ClockWordMarks.prefixMarks_joint_measure` 得到clock权重乘freshExecutionLaw。独立性没有作为本模块的新未证假设；也没有在自旋依赖的退出时刻重新假定等待或mark独立。所有实际word无重identity由既有word构造保证；对人为重复identity的非实际字，freshRun仍按identity复用同mark，代码不声称重复occurrence有独立新mark。

`endpoint_measure_mixture` 对全部实际有限字作可数不交分割，实际word z始终落在自己的fiber，集合union覆盖整个样本空间，再用measure_iUnion/tsum_congr推出无条件mixture。该等式对固定实数t给出端点分布；不是输入一个条件分布再当成证明。

## 4. 全集合stateAt与有限Config restriction精确区分

`stateAt` 存真正Finset冻结态；`endpoint_eq_clippedConfig` 仅把它送到有限采样窗内的Config。因此一般任意D/I/S可能含窗外点，endpoint只是一份restriction，不能自动判定全部任意I。

具体 `actual_protected_present_iff` 只取真实 `protectedSites L = innerD ∪ 外四邻边界`，L≥40，并调用已验收 `ProtectedDomainClockComparison.protected_present_iff`。后者通过真实image_protectedVertices把全I的每个点都表示在该有限窗中，故此时全部finite protected spins为true确等价全I⊆stateAt。S无需另假设在窗内，因为被测试的这个具体I本身完整可见；结论没有无条件推广到任意I。

`actual_protected_survival_measure_mixture` 用上述点态集合等价，把实际全I仍存活事件变成finiteConfig可测事件，接固定t真实mixture。`stateAt_protected_iff/missing_iff` 证明这里含I是所有实际chronological前缀未曾失守的准确事件，`stateAt_eq_stoppedTrajectory` 的fallback任意说明没有未来窥视。

`stateAt_geometricGood_before_loss` 以冻结state仍含具体protectedSites的前提，借前述严格n<exit等价与上一已验收Good定理，得到实际GeometricGood。并未宣称失守后的冻结state还含保护域或还Good。

## 5. 消失比较方向与当前真正缺口

`original_extinction_measure_le_frozen_protected_missing` 先接既有actual原clock endpoint消失≤未冻结modified末态缺具体I，再用“末态缺失是某个前缀缺失”的k=len见证，推到冻结态缺I。方向正确：后者记录曾经失守，因此是更大事件。没有宣称退出后冻结state依然被raw过程逐点支配。

这里左侧的“original”精确是代码中既有 `ClockExecutionLaw.endpoint` 的真实有限时钟过程；不能跳过先前比较接口直接说它已经证明原无限同步CA的τ尾界。所有概率均沿原rate-one clock/fair-mark product measure，未把事件索引当成物理时间或换掉边界条件。

实际 `measurableSet_actual_protected_survival` 经具体protectedI完整表示的点态等价，把全I存活事件识别为finiteConfig可测事件的endpoint preimage；缺失事件再用compl，因此二者均真实可测。

两个模块目前只接通固定t的真实冻结端点law、可测事件和mixture。即使正式构建/内核通过，仍不自动得到：跨所有t的同一路径停止过程相容、物理首失守时刻可测/停时性质、跨t事件字一致性、强马氏、补偿/生成元或Dynkin公式、二次尺度CMST/FSS核心概率、最终原量词恢复主定理。存在∞的首失守索引继续保留。

## 信任与验收待办

当前实际两源未见sorry/admit、自定义axiom、unsafe、native_decide或implemented_by；本次已进一步核全部41个实际专项输出、2109全分析输出和126核心输出，均只标准三公理。全部163源码hash、152个旧分析证明模块不变及8核心源已独立核对。build/audit均退出0、trust0、无新增Leanwarning。独立代理没有编辑任何Lean或重复构建。

### 冻结声明覆盖注意

最终源码共33条theorem、41个具名def/theorem/instance；其中 `freshExecutionLaw_probability` 是实际命名instance。首次专项脚本只枚举def/theorem/abbrev，遗漏它，独立代理指出后根代理修正脚本加入instance。最终专项已补齐41项，命名instance的实际输出亦已核只有标准三公理。此为已修复的审计覆盖细节，没有因此重复完整全局Lean构建。

## 最终验收绑定

- 统一成功时间：2026-10-19T20:47:19.233383+08:00；实际155分析源集及全部hash精确匹配，全部2109生成声明与实际公理输出名一一匹配。
- 最终专项时间：2026-10-19T20:48:27.411046+08:00；2源实际声明表41项与专项JSON/actual log精确一致，含named instance，无遗漏、重复或非常规公理。
- 核心历史成功记录仍复用，本次再次核8源hash及126项实际输出。旧152个分析证明模块hash无变；恰新增2模块。入口旧Good说明已修正，并随这次必要统一构建/内核审计真实重新绑定。
- 当前确定性永久冻结字、固定物理t真实joint/mixture和具体保护存活/缺失比较已通过本次内部验收；跨物理t的事件字前缀一致性、真正物理停时/生成元和CMST/FSS概率核心仍缺，完整主定理未完成。
