# 无限整数格与有限方形连接：独立 AI 语义复核

复核日期：2026-10-15。复核者为独立子代理 `/root/independent_grid_audit`，未编写或修改本阶段 Lean 证明。本文属于独立 AI 复核，不是人类数学专家签署，也不证明完整主定理已经完成。

## 范围及当前结论

只读核对十三个新模块：`InfiniteGridModel`、`SquareGridEmbedding`、`FairMarksTransport`、`RecoveryTimeTransport`、`InfiniteGridRandomDynamics`、`InfiniteGridRecoveryTime`、`SquareGridLaw`、`InfiniteGridTranslation`、`InfiniteGridTranslationLaw`、`InfiniteGridComplement`、`FairMarksPastFuture`、`SquareDeterministicRestart` 和 `SquareRandomRestart`；并与核心项目 `MathResearch/Grid.lean`、`Majority.lean`、`Dynamics.lean` 以及有限侧 `SquareTasks`、`SquareSpin`、`SquareDynamics` 的定义比较。最终统一内核审计记录与源哈希已独立补核，见下节。

在已读范围内没有发现具体语义错误。此结论受本页范围和最终源哈希约束，不是“绝对无漏洞”保证。下列判断来自实际源码，而非模块名或已有摘要。

## 逐项核对

1. **无限模型迁移。** `Site=Int×Int`；north/east/south/west 分别为对应坐标加减 1；棋盘颜色为整数坐标和模 2 等于 0。`majority4` 与核心 `Majority.update` 逐项相同：只读四邻点，不读中心，true 数严格大于 2 为 true，严格小于 2 为 false，恰好 2 才读 tie。`system` 的相反颜色局部性和零保持均由真实规则证明。分析侧显式迁移源码，并未混入不同工具链的核心 `.olean`。
2. **支持封闭。** `Inside L z` 是半开方形 `[0,L)²`，`Supported` 要求域外为 false。外点至多一个内部邻点由六种不同方向对分别推出 `Inside L z` 的反证建立，未作为未经证明的结构假设。`L=0` 的空域也在量词范围内；更新和同步／交替支持保持是实际推论。`finite_absorption_comparison` 明示以存在有限命中为前提，只是条件比较引理，不能据此宣称真实过程必然消失；本阶段扩展首达连接不依赖这个前提。
3. **嵌入及边界。** 有限顶点为 `Fin(n+2)×Fin(n+2)`，不是边长 n。`embed` 把两坐标原样转成整数。`extend` 先判定两整数坐标同时处于 `[0,n+2)`，之后才调用 `Int.toNat`；负坐标不会别名到原点。四方向等式显式分越界和域内：上、右越界以及下、左负坐标均读 false，未把有限侧 clipped 候选当成实际边界邻点。`ones_eq_four_inputs` 和明确的加法重排连接有限计数与无限四输入多数。
4. **完整轨迹及相位。** `synchronous_extend` 和 `alternating_extend` 的结论是整个 `Z²→Bool` 配置函数相等，域外由真实支持不变处理，不只是限制到有限顶点。对任意 Supported 无限初态又经 `extend_restrict` 给出版本。原点嵌入保持棋盘颜色；phase 表示初始化颜色，第一正时间槽更新 `!phase`。两侧输出时间 `t+1` 都使用 marks 的时间 `t+1`，时间零硬币存在但未被更新读取。
5. **整场联合 law。** `FairMarksTransport.pullback` 用任意索引注入选择整个积场。可测性逐坐标由投影得到；`map_pullback` 调用实际 mathlib `Probability/Independence/InfinitePi.lean` 的 `map_infinitePi_infinitePi_of_inj`，该引理确实覆盖任意索引族的独立概率积，结论是整个积测度的映射等式，不局限于有限前缀，也不需要索引类型上的可测结构。共同的公平边缘来自 `FairMarks.markMeasure` 的真实无限积定义。`SquareGridLaw.eventEmbedding` 实际定义为 `(v,j) ↦ (embed v,j)`，其注入性从空间注入和时间坐标相等推出；`restrictSample_map_measure` 由该证明取得整个有限时空场的实际 law，没有把 law 当作输入。
6. **无限配置的可测性。** `InfiniteGridRandomDynamics` 的样本是真实全格／时间公平积场。局部更新从四个配置坐标及一个标记坐标组合到有限 Bool 五元组，再套用多数规则；这里仅对有限 Bool 元组使用可数性可测结论。全配置及时间切片采用 `measurable_pi_iff`，没有错误地把整个无限配置空间当成有限状态。`Z²` 是可数坐标集，全零配置单点的可测性可由现有实例取得。
7. **保留无穷的首达。** `RecoveryTimeTransport.time_le_time_of_zero_imp` 对比较对象先分 infinity 与有限值；无穷分支用 `le_top`，有限分支只从已经有限的首达值抽取命中。`time_eq_of_zero_iff` 由两个方向推出等式，不以所有样本有限命中为前提。`InfiniteGridRecoveryTime` 在实际全格样本上使用同一个 `ExtendedRecoveryTime.time`：未命中样本为 infinity；可测性不依赖有限支持或有限命中，尾事件等价只使用已经证明的零吸收性。
8. **实际 recovery law 与尾界连接。** `SquareGridLaw` 的两条随机完整配置等式沿用相同样本的 restricted marks；零事件由 `extend_eq_zero_iff` 严格等价。`synchronous_recovery_eq`、`alternating_recovery_eq` 因而对所有样本，包括 never-hit 样本，得到 `ℕ∞` 逐样本等式。恢复时间 pushforward 等式再由真实 `restrictSample` law 和两侧时间可测性推出，尾概率由对应可测事件的原像得到。对任意 Supported 全格初态提供的版本只使用已证 `extend_restrict`。末尾 `two_way_clock_tail` 从已验证有限侧比较替换实际全格恢复尾；时钟一侧依旧是有限系统的端点非零概率，不能据此改称已经定义了无限格连续时间吸收时间。
9. **平移方向与奇相位。** `shift a z=z-a` 和 `translate a f(z)=f(z-a)` 将原点图案移至 `+a`；`InsideTranslated L a z=Inside L(z-a)` 使用同向平移。四方向与 shift 交换已经逐方向证明。`colour a=true` 表示偶坐标和平移；`colour_shift` 在偶平移保持颜色，奇平移取补。`translatePhase a phase` 相应偶保持、奇取补，且证明了全时间槽的 `activeColour` 恒等式，随后用于整个交替轨迹等式。真实样本平移的索引仍为 `(z,j)↦(z-a,j)`，时间坐标不动；注入性实际证明后由整场 law 得到测度不变。同步和正确相位的交替恢复 map 由逐样本 `ℕ∞` 等式取得，包括 infinity，无有限命中假设。
10. **全一背景和标记补。** `InfiniteGridComplement` 的四输入恒等式同时补全部邻点和 tie；随后同步／交替轨迹均同时补初态和全部 marks。它没有错误声称固定同一硬币就得到互补轨迹。单硬币补保 law 通过公平测度两个 Dirac 项交换证明；整个时空场补保 law 再由 `infinitePi_map_pi` 得出，不只检查单硬币。`targetOneSynchronous` 是实际首次命中全 true 配置的 `ℕ∞` 时间；全一命中事件与补过程全零命中事件逐时刻等价，故得到逐样本等式及真实首达 law 等式。当前针对 target-one 的明确恢复 law 定理是同步版本，交替有轨迹互补恒等式。
11. **真实确定时刻重启。** `FairMarksPastFuture.past` 只读取所有站点的正时间槽 `1,…,s`；`future` 对时间零槽读取原来的 `η(v,0)`，对正槽 j 读取 `η(v,s+j)`，没有错误地把与过去重叠的 `η(v,s)` 当成独立未来零槽。其索引注入性、与使用过的 past 索引范围不交、完整 future law 及整场 past/future 独立性均实际证明，包含 `s=0`。所称独立历史是“使用过的正槽历史”，不包含未使用的时间零硬币。
12. **当前状态独立性及乘法界。** `SquareRandomRestart.fillPast` 以给出的正槽前缀重建样本，前缀外置 false；`synchronous_eq_of_agree_upto` 通过真实递推证明当前状态不依赖这些填充值，故当前状态可测地因子化到 past，进而与 future 独立。确定重启从实际时间 `s` 状态出发，与正槽重编号相合；非零事件同时蕴含当前非零（零吸收性）及同一 future 从 top 出发在 t 时非零（单调性）。真实概率的乘法上界由这两个独立事件的交和整场 future law 推出，未把 Markov 性或 law 作为未证明输入。块界的底数是实际 top 在 b 时的非零概率；`j=0` 给概率不超过 1，`b=0` 也只是平凡界。尚未证明底数小于 1，不能把该幂次形式直接称作已得严格几何衰减，更不能从中声称二次期望界。
13. **最终包装接口。** `SquareRandomRestart.recovery_block_le_pow` 通过已证真实恢复尾等价把非零状态幂界改写为 `ℕ∞` 首达尾；没有截去 never-hit 样本。`SquareGridLaw.translated_supported_recovery_map` 连接已经证明的任意平移首达 law 与 Supported 初态有限侧 law；`supported_tail_le_top` 使用实际初态单调性；`supported_recovery_block_le_pow` 把同一个真实 top 概率幂界搬到无限格 Supported 初态。它们没有增加严格收缩或 CMST／FSS 尾界假设，因而仍保持上项所述的尺度与期望限制。

## 构建、内核及公理记录的独立复核

复核于北京时间2026-10-15 12:26完成，机器可读记录为 [infinite-grid-semantic-validation.json](infinite-grid-semantic-validation.json)。本子代理没有重复运行 Lean 构建，而是核对真实构建／审计记录、实际审计命令的脚本以及当前全部源文件；语义审阅与证明作者分离。

- 分析统一记录为 [analysis-validation.json](analysis-validation.json)，时间 `2026-10-15T12:25:29.270763+08:00`。新增13模块157条公开定理；目前89个分析模块、1108条公开定理、90份分析 Lean 源（含总入口）。逐文件重新计算这90份源的 SHA256，全部匹配统一记录；实际文件集合也完全一致。
- 核心保留此前 `2026-10-14T21:18:34.078751+08:00` 的成功审计记录，没有为本阶段重复构建。8份核心源当前 SHA256 全部匹配原记录。两项目共98份正式源均已复算，不以旧摘要代替当前源核对。
- [analysis-build.log](analysis-build.log) 与 [analysis-axioms.log](analysis-axioms.log) 均为 `EXIT_CODE=0`。实际审计入口含1108条 `#print axioms`，逐一与日志的1108条声明结果对应，无遗漏或重复。分析记录命令为 `lake env lean --trust=0 AnalysisAxioms.lean`，信任级别0。此次统一分析构建没有 warning；历史基线中的依赖本地变更提示属于旧日志，未复制为本次新 warning。
- 核心审计入口的125条公开定理加1个模型定义，共126条声明，与 [core-axioms.log](core-axioms.log) 的126条结果逐一匹配；原记录使用 `lake env lean --trust=0 audit/CoreAxioms.lean`，两个退出码均0。
- 两份公理日志实际出现的依赖集合均仅为 `Classical.choice`、`Quot.sound`、`propext`，没有 `sorryAx`、额外自定义公理或 error 记录。结合作者统一源码禁用构造检查与本次逐声明核对，在该冻结源集合内没有发现占位证明或未经证明的新增核心概率输入。

## 未覆盖及不可宣称的结论

- 有限方形桥接当前直接采用原点方形、全零外背景、边长 `n+2`；另已证明任意平移的真实轨迹／恢复 law（含奇平移 phase 翻转）及状态／标记补对称和同步全一目标首达 law。边长 0／1、原问题采用的直径与 n 的关系、任意有限扰动的归一化及最坏初态／上确界的精确量词连接仍需后续证明，不能把这些已闭合的对称性自动当作完整原命题等价性。
- 尚无完整 `tau(n)=Theta(n²)` 的最终 Lean 定理，因此不能声称已经核对了原始数学命题与一个已完成 Lean 主定理的严格等价。
- CMST／FSS 的核心上下尾仍未自含形式化。真实确定时刻同步重启和基于实际 top 概率的块幂界已建立；实际底数的严格收缩、适合二次时间尺度的估计、期望及最终统一常数并不由本阶段桥接引理自动得到。
- 这次核对证明记录及对应源集的内核验收成立，不提供编译器供应链认证，也不能用一次独立 AI 审阅代替人类专家认证或完整主定理的最终语义验收。
