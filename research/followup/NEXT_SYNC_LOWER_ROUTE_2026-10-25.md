# 把已证时钟慢恢复接回同步下界

2026-10-25。只读接口核查；以下连接与数值步骤均待新Lean验收，本次没有新增或构建Lean。上界的FSS自含核心仍是另一条路线。

**尺寸与已证起点。** 设K=12288000、半宽L、有限模型参数n=`ClippedSquareCoordinates.parameter L=2L−1`，原方框边长为N₀=n+2=2L+1。`PhysicalWeightedDrift.original_clock_extinction_at_quadraticHorizon_le_half`已给L≥K、T=L²/K处原时钟灭绝概率≤1/2；`topConfig n`与该定理的`fun _=>true`定义相同。

**最短现成接口。** 直接用`SquareGridLaw.two_way_clock_tail n c k`的第一项：

$$P_{clock}(\text{仍非零于 }s_k)\le P_{sync}(\tau>k)+\varepsilon_{n,k},\quad s_k=8\log2(k+1),\quad\varepsilon_{n,k}=\tfrac65(n+2)^2 2^{-(k+1)}.$$

其中同步尾属于无限格上的`InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n (topConfig n))`，不是新的假设。底层方向是`ClockRecoveryComparison.clockProbability_le_scan_add_completion`和`SynchronousClockComparison.scan_next_le_synchronous`；`SquareRecoveryTime.two_way_clock_tail`再由`SquareGridLaw`运输到原格点law。第二项“scan/sync≤clock+rank”不能用于推出同步慢。源码中没有`ScanGridRecovery.lean`，相应连接已经在上述模块。

**待证的时间与误差算术。** 可取更保守的L≥16K，q=L² div(16K)、k=q−1。需实际证明q≥L、k+1=q、sₖ≤8q≤L²/(2K)≤T，以及k≥L²/(32K)。再证明ε≤1/4：n+2=2L+1≤3L，q≥L，而对L≥16可用归纳证明2^L≥64L²；于是ε≤54/320<1/4。这些具体常数是接续方案，本次尚未kernel验证。

从T的半概率结论转到sₖ，**必须保证时间方向正确**：sₖ≤T且时钟灭绝CDF单调。现成`ClockWordConsistency.reverse_word_prefix_ae`、`EventTrace.execute_append`和`SquareSpin.updateEvent_zero`可供补出端点零状态持续与CDF单调；目前未找到现成完整`clockProbability`时间单调引理。更短的替代是直接使用已证`PhysicalWeightedDrift.original_clock_extinction_le_linear_time`于sₖ，并以非负系数18L+12和`quadratic_bound_le_half_threshold`控制分子，这样无需新证明clockCDF单调。还需用可测端点事件及概率总质量1，把灭绝≤1/2转换成非零≥1/2。随后第一比较式给同步P(τ>k)≥1/4。

**保留∞的期望与奇偶尺寸。** 补一个非负扩展积分下界：`ExtendedRecoveryExpectation.expectation μ τ ≥ (k:ENNReal)·μ{τ>k}`，由尾集的常数指示函数≤`τ.toENNReal`及`lintegral_mono`推出，不能改用把∞变成0的`toNat`或未证可积的Bochner期望。`SquareRecoveryTime.synchronous_tail_probability`、`SquareGridLaw.synchronous_tail_probability`和`HomogeneousRecoveryTime.synchronous_eq_zero_background`已有；运输期望可用`ExtendedRecoveryExpectation.expectation_eq_of_map_eq`与`OriginalRecoveryProfile.expectedRecovery_finite_square`。由此候选下界为奇数边长图形Eτ≥L²/(128K)。

一般恰N取L=(N−1) div2、N₀=2L+1≤N。若N为偶数，先用`SquareGridLaw.supported_tail_le_top (N−2)`，将小奇数实心方块在同一N方框内的同步尾下界传给N实心方块，无需假定τ(N)单调；小方块支持于大方框只需整数坐标包含。最后`PerturbationSymmetry.distance_square`与`OriginalRecoveryProfile.square_expectedRecovery_le_tau`保证恰N量词。对足够大N可保守用L≥N/6，得到候选τ(N)≥N²/(4608K)。以上奇偶、支持、取整与扩展积分连接仍待证明；不等于主定理已经完成。
