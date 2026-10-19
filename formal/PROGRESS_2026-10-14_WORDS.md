# 实际事件字、标记联结与有限核阶段

统一验收：2026-10-14 16:32:59，北京时间。06:40 指定唤醒接续后，用户再次要求继续；本阶段完成后，按最新用户要求暂停新增证明并整理成果。

**完整同步 CA `τ(n)=Θ(n²)` 主定理尚未通过 Lean。** 本记录覆盖实际模型连接及有限核基础，不将执行重排等价、Gibbs 平稳性或零温极限扩大成 PW 删更新定理或 CMST 方岛定理。

## 验收与工具链

分析工程新增21模块、313公开辅助定理，现有60模块、814公开定理、61项目Lean源文件。总构建和814条逐定理公理审计退出0，公理仅 `Classical.choice`、`Quot.sound`、`propext`。无 `sorry`、`admit`、自定义公理、`unsafe`、`native_decide`、`implemented_by` 或跳过内核构造。九个依赖本地改动提示保留，自有源无linter/module警告。逐模块数量与全部源码哈希在 `audit/analysis-validation.json`。

核心工程未改：7模块、125公开定理、1模型定义、8源文件，原有验收哈希继续匹配。总计939辅助定理包含基础引理及显式迁移的证明，不能当作939项独立成果。

核心使用Lean4.35.0，分析使用Lean4.35.0-rc4及锁定mathlib `54c01c3314d33d15d77893cbe4e0472ff26bb34d`。EventTrace和BipartiteDynamics的必要核心源码已在分析namespace显式迁移并重新构建，未加载核心工程异版本olean；未重置或重新下载依赖。

## 新增模块对应

| 连接 | 模块及公开定理数 | 已闭合内容 |
|---|---|---|
| 事件字与rank概率 | ClockEventWord 28；FiniteRankWitness 16；SquareGreedyPaths 20；ClockRankTail 8；SchedulingFailure 5 | 实际有限事件字及可测性、rank实际链见证、五邻路径枚举和闭合概率尾、联合调度失败界 |
| 实际标记分布 | FairMarks 10；ClockWordMarks 6；ClockExecutionLaw 14；ClockSelectedMarks 22 | 真实公平乘积、只依赖时钟且不复用身份的选择律、事件字纤维联合law、全部正层任务标记law及与整时钟样本独立 |
| 实际局部更新及排序 | SquareSpin 27；EventTrace 12；MarkedEventTrace 10；RankSlotEmbedding 20 | 真正四方向固定零输入、具体更新交换、同身份及冲突顺序的终态等价、实际rank/颜色槽排序 |
| 真实轨迹连接 | BipartiteDynamics 20；SquareDynamics 17；ClockSelectedWord 18；SquareBatch 12 | 实例化同步/棋盘拆分、任务删选字与层字等价、同色批次等式、层字=实际交替轨迹 |
| 有限温度与零温基础 | ZeroTemperature 9；FiniteWordKernel 12；SquareGibbs 12；SquareGibbsLaw 15 | 有限更新核极限=真实公平标记执行积分、固定零边界能量局部恒等式、有限归一化质量、详细平衡及平稳性 |

## 概率输入已经解除的连接

`ClockEventWord.word ω t` 以 `(站点,响铃序号)` 为身份，按真实chronological到达从新到旧排序。异常样本使用明确默认值，仍保留原始事件集定义；模型提供共同AE有限性、正性与无同刻，使该word几乎处处精确覆盖所有到达时间 `≤t` 的事件。word无重复与严格时间次序是已证性质，word及其长度/位置选择均可测。

`FiniteRankWitness.annotate` 使用与核心相同的newest-first前驱最大值递推。从真实rank成员构造原word反序的子链，长度等于rank，并可截取任意正长度 `q≤rank`。这些见证不是输入。`SquareGreedyPaths` 用真实非周期四邻加原地的五方向编码枚举长度q空间路径，路径数至多 `N·5^(q−1)`。重复编码只减小基数，不假设路径间独立。接GreedyClockChain后，`ClockRankTail.rankLarge_half_tail n t q hq` 只有 `n,t,q,0<q` 参数：

\[
\mu_{clock}(rankLarge(n,t,q))\le \frac{(n+2)^2}{5}e^{9t}2^{-q}.
\]

`SchedulingFailure` 取 `r=k+1`、`time k=8 log(2)r`、`rankThreshold k=128r`，定义bad为rank过大或真实前r正任务层最大完成时间超过time。真实两尾界合并得到

\[
\mu_{clock}(bad(n,c,k))\le \frac65(n+2)^2 2^{-r}.
\]

这是时钟调度事件的联合界，没有使用CA消失概率、PW或CMST。

`FairMarks` 实际构造 `(1/2)δ_true+(1/2)δ_false` 及其无限坐标乘积，与时钟空间取乘积。对clock-only可测身份选择，有限公平乘积律从固定身份注入映射及真正乘积积分推出。`ClockWordMarks` 在实际word长度足够的事件上，用word无重复证明prefix身份注入；`ClockExecutionLaw.endpoint_joint_measure` 在任意真实word纤维上保留任意额外时钟事件，得到真实终态联合law。重复身份word的纤维由已证word无重复推出为空，没有把Nodup作为最终概率输入。

`ClockSelectedMarks` 明确定义前 `k+1` 正层的实际任务集合，证明真实selectedIndex/eventId可测及选择身份共同AE注入，推出所有选中标记的有限公平乘积律和与完整clock sample独立。没有用随机选择当前gap独立这一错误推断，也没有将未来Poisson向量强Markov作为参数。

## 执行、相位与边界

`SquareSpin.ones_eq_four_inputs` 显式证明内部邻居计数等于四方向Bool输入之和，越界方向输入false，阈值始终为2。不能解释为只对内部邻居做多数。真实规则消解局部性、全零保持、共同标记单调性及无冲突事件交换。

`RankSlotEmbedding` 对实际annotate结果按 `2rank−1/2rank` 颜色槽mergeSort；已证明事件身份、冲突次序、同槽同色与站点不重复，具体执行终态相同。最终接口没有rank增长或commutes输入。

`ClockSelectedWord` 在真实 `squareMaximum n c k≤t` 条件下，将任务事件身份定位到完整clock word，证明删选后的chronological字与层顺序字同事件、同冲突次序及同标记执行终态相同。`SquareBatch` 再证明完整同色任务层等于真正checkerboardStep，任意样本上的层字执行等于

`SquareDynamics.alternating (chosenMarks ω η) initial (!c) (k+1)`。

因而在共同AE事件和完成时间条件下，真实时钟删选字就是该实际交替轨迹。索引约定：k包含前k+1正层，正层j使用tasks n c (j−1)，初始化phase=!c。SquareDynamics的同步拆分保留同一预先给定逐槽标记，不额外声称两条完整链独立。有限吸收比较仍有有限吸收见证这一结构条件，未自动推出恢复时间有限。

## 零温与Gibbs的精确覆盖

局部场为 `h(f,v)=2·ones(f,v)−4`；热浴更新到true的概率为 `(1+exp(−2βh))⁻¹`。`ZeroTemperature` 证明其β趋向正无穷时变为严格多数确定值／平局1/2，并归纳证明任意固定有限更新字的算子收敛。

`FiniteWordKernel` 由实际有限乘积测度的首坐标分解、测度保持映射和积分，证明公平标记执行均值等于实际多数核递推；进而把上述零温极限接到真实执行测度积分。身份Nodup是该有限字引理的结构条件，允许同一站点多次更新；实际clock word本身已提供该条件。

`SquareGibbs` 采用内部无向相互作用加固定外零边界能量，证明

\[
E(f^{v,+})-E(f^{v,-})=2h(f,v)=4\,ones(f,v)-8,
\]

并把真实两指数权重条件比接到热浴logistic概率。`SquareGibbsLaw` 构造严格正配分函数和总和为1的有限实数概率质量，证明实际单站核行和为1、详细平衡与平稳性。当前使用有限质量函数形式，未包装成全局Measure/PMF对象；尚未证明PW所需的单调密度保持及删更新随机偏序不等式。

## 独立复核与剩余工作

关键独立复核：`audit/clock-rank-tail-review.md`、`rank-slot-embedding-review.md`、`clock-marks-review.md`（另独立检查30公开定理和5概率实例）、`clock-execution-law-review.md`、`clock-selected-marks-review.md`、`finite-word-kernel-review.md`、`square-gibbs-review.md`、`square-gibbs-law-review.md`。独立AI复核不能替代外部数学审阅；实际可信证明以Lean内核、完整公理审计及源码哈希为准。

下一阶段仍需真正证明有限温度PW删更新及零温传递、CMST二维方岛定理、两向恢复事件随机比较、实际块重启与期望界、尺寸嵌入和统一常数。核心已有整数格点支持封闭性，本轮分析采用边长n+2的有限方形；最终仍须把参数与原问题完整连接。泛型块尾工具、有限Gibbs平稳性和相同事件重排均不能替代这些证明。

01:34的公开解答检索报告已保存，本次未重复启动检索；未检出同模型公开解答不证明开放性或新颖性。回归13/8未解。按用户最新要求，本阶段验收后暂停新增证明；两次指定调度均已处理并停用，无新调度、无运行中子代理、无外部联系或发布。
