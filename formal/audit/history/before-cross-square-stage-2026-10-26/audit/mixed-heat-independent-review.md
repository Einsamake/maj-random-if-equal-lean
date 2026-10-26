# 实际热衰减、局部清空与时钟限制阶段：独立语义复核

结论：本阶段十一份非本人撰写的数学源均已逐条核对，未发现语义漏洞。已证明真实原law下的热衰减、右半粒子数方差与局部清空概率，并完成真实时钟/身份标记的注入投影law及实际更新字限制；完整原同步二次上界仍未完成。实际统一构建与标准Lean --trust=0输出的全源/名字/顺序对应由 mixed-heat-independent-final-binding-evidence.json 绑定。旧249源记录不能认证本阶段新增证明。

复核者为 AI `/root/heat_stage_review`，未撰写本轮任何 Lean 数学模块。独立 AI 复核不等于人类专家认证，也不是公开解题或新颖性认证。

## 数学含义核对

1. **有限路径确实相同。** FiniteSlotPoincare 用真正的零延拓把 Fin n 上的顶点求和接到 Nat 的 range n。边集合为左端值加1等于右端值，每个 range(n−1) 的 k 唯一对应 (k,k+1)，通过双射完整核对，无重复边或丢失端点。n=0、1 的退化路径亦包含在陈述中。实际中心场的总和为0由已证明的原law质量守恒解除，得到 H≤(2M)²E=4M²E，M=parameter L+2，不把通用Poincare输入留给真实过程。
2. **热衰减来自真实能量。** ScalarHeatDecay 直接对 H(t)exp(ct) 用乘积法则，再由[0,∞)连续、内部导数非正推出反单调；没有在t=0强行要求双侧导数，也未把指数衰减当输入。MixedHeatDecay 接入真实 H′=−E、H0=M/2 与实际Poincare，得到 H(t)≤(M/2)exp(−t/(4M²))。保守时间是16M²，exp(−4)≤1/8给H≤M/16；没有把先前略不足的8M²当成已证常数。每条物理邻边计一次，率1/2已经在旧能量恒等式中正确消去，没有再多乘或少乘2。
3. **数的是实际同一样本右半槽的粒子。** MixedRightCountMoments 的J是原 ClockWordMarks.measure(parameter L) 下同一个实际endpoint的占据和。右半槽基数确为M，通过显式双射证明；J与旧YoungParticles.rightCount逐样本相同。先证明可测、可积、平方可积，才把真实期望与有限和交换。二矩使用同一样本两因子，g的对角等于rho，只有i≠j才使用已证明的非正协方差。由此得到 Var(J)≤Σright rho_i(1−rho_i)≤M/4；没有假设不同槽独立。L²与标准Mathlib variance的对应已明确证明。
4. **均值与概率输入实际解除。** MixedRightCountHeat 对真实右M槽使用Cauchy，得 (EJ−M/2)²≤M H；16M²时由H≤M/16推出EJ≥M/4。通用 CountLowerTail 的均值、方差、L²前提在 MixedClearingProbability 中全部用真实过程定理解除。J<N且N≤M/8蕴含|J−EJ|≥M/8，真正Mathlib Chebyshev给原law ENNReal概率≤16/M，不曾把(EJ)²当成E[J²]。
5. **局部白块与尺寸没有偷换。** 单调配置中N≤rightCount等价于可用域内的西南N×N全白；N=0单独处理，反向等价显式要求N≤M，避免不可用格点造成真空结论。实际endpoint单调性来自已证明更新不变性。辅助L=4N在N≥1时实际边长M=8N+1，N≥8给M≥65，失败概率≤1/4；真实辅助物理时刻16(8N+1)²≤1296N²。最终陈述仍然是大辅助mixed方块中的局部白块，不能当成小原方块或原同步过程已经得到二次上界。辅助mixed全白不是吸收态，本阶段只用固定时刻事件。
6. **限制law是真实乘积law。** ClockSampleRestriction 的event注入保留(site,k)中的k。clock与mark分别按同一event注入投影，经实际infinitePi注入映射定理及prod map得到完整联合原law。gap、原arrival、clipped chronologicalArrival、eventTime和mark逐点保持，包含异常样本；有限事件集为真正逆像，Good及单一满概率集上∀t的Good确实随注入保留。这不需要几何邻接保持，也没有隐含endpoint或更新字限制结论。

7. **排序限制保持真实执行顺序。** ClockWordRestriction 在大样本Good上证明 smallword.map(eventι)=bigword.filter(range eventι)，通过真实coverage与同一严格时间排序的唯一性证明等式；反序后的实际执行顺序也保持。该结论没有错误延伸到异常fallback样本。共同AE∀t由已有真正good_ae直接获得，并由fst准保测映射提升到原clock/mark联合law；没有把每个固定t的AE偷换成∀t，也没有重采样所保留的身份mark。此处只证明word限制，没有声称几何或endpoint耦合。

## 明确边界

本轮保留真实law、物理时间、原模型以及∞恢复时间定义，没有改动原同步exact-N下界。M始终为parameter L+2，仅L≥1才可写成2L+1；L=0的实际边长是2。新的时钟投影law不等于跨尺寸更新过程已比较。真实投影law和word限制现已完成；仍需几何/每event更新的跨尺寸保持或支配、局部白块转原过程清空、原同步比较与真实重启，才能得到最终原exact-N期望上界。完整Theta主定理尚未完成。

## 冻结后已阅读的十一份源指纹

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

## 实际验证边界

本轮真实统一验收时间为2026-10-26T14:36:47.895458+08:00：252分析源、3238分析定理；沿用并逐源回核旧core的8源和125定理+1模型定义，共260正式源、3364实际全局公理输出。core本阶段未重新编译，不能把旧core构建日期改称本轮日期。新增11模块65定理78具名声明，七组专项记录须同时与冻结源、打印表、实际build0及标准trust0输出绑定。公理仅Classical.choice、Quot.sound、propext，无自定义公理或占位；仅旧batteries工作副本提示，无新增Lean warning。完整证据绑定以实际执行的独立脚本输出为准。
