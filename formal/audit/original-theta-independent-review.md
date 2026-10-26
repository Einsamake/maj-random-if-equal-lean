# 原同步 exact-N 二次阶主定理：独立语义复核

结论：当前最终七份证明及本轮前一阶段十一份证明均已由非作者逐条阅读，未发现语义漏洞。最终定理已解除概率、耦合、重启和有限期望等核心结论输入，给出了原模型最坏扩展期望的标准渐近二次阶。全267份正式源和实际标准内核输出的对应由 original-theta-independent-final-binding-evidence.json 独立绑定，不能以旧260源记录认证新增证明。

复核者为 AI `/root/heat_stage_review`，未撰写这十八份 Lean 数学模块。本结论是独立AI复核，不是人类专家认证、首次解决认证或公开文献穷尽检索。

## 1. 最终陈述的确切含义

`OriginalQuadraticRecovery.tau_quadratic_bounds` 对每个 N≥786432000 给出

    ofReal(N²/56623104000) ≤ OriginalRecoveryProfile.tau N
                           ≤ ofReal(664066*N²).

`tau_theta_quadratic` 没有外部参数或欲证核心结论前提，显式给出正数 c=1/56623104000、C=664066 和阈值 N₀=786432000，证明阈值以后的两侧界。上界本身对 N≥16 成立。此为标准渐近 Θ(N²)，不是声称同一显式常数对所有N≥1成立；历史 `ca_clean_proof.md` 候选稿中“all n≥1”的更强字面陈述不属于本次定理。

期望及tau始终取ℝ≥0∞，首达时间取ℕ∞。没有通过把∞转为0的toNat来假造有限期望；有限均值和大尺寸配置的恢复时间几乎必然有限均应作为上界的结果。

## 2. 与原问题的模型和量词核对

本次直接读取[作者原始PDF](https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf)的§1.2(p31)、§4.1(pp53–54)、§4.2(p54)及Q7.4(p79)：原模型为Z²同步四邻多数，平局逐格独立公平；尺度为容纳扰动的最小平移半开轴方盒边长；tau取确定初态在精确直径N时的最大期望首次恢复到两个同质背景之一的时间。这些要素与当前Lean定义逐项一致。arXiv HTML此次请求超时，成功核对的是作者期刊PDF；不据此判断2026年文献状态或优先权。

代码中 `InfiniteGridModel.majority4` 不读中心，`InfiniteGridRandomDynamics` 用真实独立fair标记，正输出时刻t+1读同一时刻标记。`PerturbationGeometry.diameter` 允许任意整数平移并保留∞，`PerturbationSymmetry.distance` 取到两个背景的最小直径。`HomogeneousRecoveryTime.synchronous` 的目标就是两个同质配置，`OriginalRecoveryProfile.tau` 对精确distance=N的确定初态优化；已有归一化、平移/补色law及最大值达到定理把sup与原问题的max连接。最终没有换成黑格数量、周期边界、异步时间或平均初态。

## 3. 热衰减和局部概率的前一阶段输入

前十一源均已独立阅读并实际绑定。Fin槽与Nat路径之间有真正的顶点求和等式和逐边双射，质量零由真实原law守恒解除；H′=−E与H0=M/2给H≤(M/2)exp(−t/(4M²))，在16M²时H≤M/16。原law的同一样本二矩展开，对角保持Bernoulli方差，仅异点使用已证明的非正协方差，得Var(J)≤M/4。真实右M槽的Cauchy界给EJ≥M/4，真实L²/Chebyshev输入全部解除，得原law下P(J<N)≤16/M。未假设槽位独立。

单调形状把N≤J转成实际西南N×N块全白，边界和N=0情况已处理。M始终为parameter L+2，L≥1时才为2L+1；辅助L=4N给M=8N+1。这里只使用固定时刻局部白块，绝不假定mixed全白是吸收态。

## 4. 真正跨尺寸耦合已经解除

`ClockSampleRestriction` 保留原(site,k)身份，分别由真实指数和fair无限乘积law推出联合样本投影law。raw和clipped事件时间逐点保持。`ClockWordRestriction` 由coverage和严格时间排序唯一性给实际smallword映回等于bigword的range过滤，并保持反序执行顺序；结论只在Good或单一满概率集的∀t下成立，没有对异常空字fallback强行作点态声明。

`SquareInclusion` 的坐标嵌入真实保留四邻位置。小方块zero-extension逐点≤大方块mixed-extension，实际majority4单调性给同mark更新比较；外部事件不写入受限小状态。`ClockRestrictedExecution` 对真实过滤字逐event归纳，保留事件在两过程执行，外部事件只在大过程执行。其通用inside/outside结构前提在square_execute_rel中由真实几何全部解除。

`CrossSquareClockBound` 再用真实word共同AE和联合样本投影law转回小方块原μ。原N边长取有限参数N−2（N≥2），实际N块全白覆盖所有小方块顶点。最终N≥16时原zero-boundary clock survival在16(8N+1)²物理时间≤1/8；没有把同尺寸比较冒充跨尺寸，也没有重采样identity marks。

## 5. 同步比较方向、数值常数及∞重启核对

`ClockEndpointSurvival` 在真实Good字上由prefix和原零态吸收证明survival随物理时间减，再在原联合law下取概率；没有声称mixed局部事件随时间单调。取k=1296N²，辅助时间≤1296N²，log2≥1/2给SchedulingFailure.time(k)≥k。调度误差使用真实原边长(N−2)+2=N：N≥16时64N²≤2^N给error≤3/160≤1/8。

使用 `SquareRecoveryTime.two_way_clock_tail` 的第二方向，真实同步尾在 b=2 rankThreshold(k)+1 时≤2*(1/8)+2*(1/8)=1/2。两个checkerboard相位的因子2和调度误差的因子2均支付，没有反用下界方向。rankThreshold(k)=128(k+1)，故b=331776N²+257≤332033N²。

`SquareRandomRestart.recovery_block_le_pow` 对每个确定小方块初态给真实块尾乘法界，使用的是已经证明的同步未来fair标记law与独立性；不是把Markov/成功概率作最终前提。概率测度有限性使.real尾界能正确转回ENNReal。`ExtendedBlockTail.lintegral_le_two_blocks` 保留可能的∞先取非负扩展积分，得E≤2b≤664066N²；不存在先假设恢复有限或可积的循环。

`OriginalRecoveryProfile.tau_eq_normalizedTau` 已有真实平移、补色、尺寸与恢复law，对所有有限初态g的统一上界解除原exact-N优化。最后与旧原同步二次下界合并，主定理无剩余核心输入。

## 6. 实际验收范围

实际global记录为2026-10-26T14:53:59.002869+08:00：258分析模块、3280分析定理、259分析源，加旧core8源，共267正式源、3406实际公理输出。分析统一build和标准Lean --trust=0逐声明审计实际exit0；公理仅Classical.choice、Quot.sound、propext，无自定义公理或占位，只有旧batteries工作副本提示，无新增Lean warning。core8源仅重核指纹和旧实际输出，本阶段未重编。

本轮分两阶段：前11源65定理78具名声明；最终7源42定理48具名声明。共18源107定理126具名声明都须再次同最终global、各组打印表/实际输出、draft字节和源指纹绑定。带撇号名字必须完整匹配，不能用截断正则计数。

## 已阅读且冻结的十八份源指纹

- `FiniteSlotPoincare`: `b0ba240acf3637175fb4de31322287a50facd55aa268ee58591171051b06a43c`
- `MixedMomentPoincare`: `e909f7316635d2957484773a7efd6a20f85894e4a0066106d01299432ca1df1d`
- `ScalarHeatDecay`: `bc5f3a9b844f563fbc0c711f2a18c65f6ef06aa0b24faea1965361775715b9b6`
- `CountLowerTail`: `e514a50e94a0830339b0d23398f7b31525653cd30896f42943f8651c8bdbd51f`
- `MixedHeatDecay`: `1b6190111d5df196beba4ee4a7c168260bcbca71448e6c2327174914034c76c9`
- `MixedRightCountMoments`: `16bb567486301f4da60c38577c4e3ffcc248b646b7288c1ebd729a536b49cce7`
- `MixedRightCountHeat`: `692240c36accdc663d54beb9eb6660a9ec47f55dab9499baf00bef5c4564c4d4`
- `MixedLocalClearing`: `0d1763b9198374a29439304d700503bb6ca778d7143616f459ad83d634b152c1`
- `MixedClearingProbability`: `448ac959d73c44f25af90475874ba12b452f755d6eca2ed4779c2491390172c8`
- `ClockSampleRestriction`: `4cbc584816e306a679ee3af0fcf407710c6b6cec6f334995a7e10cc33e3587ce`
- `ClockWordRestriction`: `1279fb3e22fe009ea2177300ae68378398f39b54602b7fea4fc94d4e22a8edfa`
- `SquareInclusion`: `9a94bbc0b71dd3cdb26dcf1aee7965f96f867950a86ea567c03bc849c73c664b`
- `ClockRestrictedExecution`: `0057322ee1490001d9b4e92eabd3c4d3b526c9b0477476b08f69753b7d716324`
- `ClockEndpointSurvival`: `f9315ff33ab2cee211cb52d14ff3a5efb3c4bcc9a969bd39d0faa93fa9787031`
- `CrossSquareClockBound`: `3d5d343a63aa0e48288457f05824f5509dd9860d8112ca88b500d5d7faf0158a`
- `SyncUpperScale`: `c757120c711baddd9ddaf5865ed0b0bbbe694c6456aa11aa722f5984407ae39a`
- `OriginalQuadraticUpper`: `6411173cd853ec57417b799a5aeeda6d316490453a31a18cf9c07296efbf5c3f`
- `OriginalQuadraticRecovery`: `27e11b9ce8afaa9d41b41f001b51444a19d293dcaf880eba2064457dfb9d758b`
