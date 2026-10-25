# 有限真实时钟 Dynkin 阶段：独立语义复核

结论：本阶段把任意有限状态机及混合边界形状的观测量，接到了原始时钟与事件身份标记的真实期望变化公式。下列七个非本人撰写模块的数学含义与其证明匹配，未发现语义漏洞；这不是完整主定理验收，也不是人类专家认证。标准内核和实际输出绑定另见同名 final-binding-evidence.json；未绑定的新旧验收不能互相代替。

## 范围与责任

独立复核者：`/root/sync_profile_review`，AI。独立审查对象为 FiniteObservedClockState、FiniteMachinePreState、MachineTraceTelescope、MachineEventScores、MachineClockDynkin、MachineClockGenerator、MixedClockDynkin。ClockTimeNullGraph 由本复核者撰写，因此不计入自己的独立语义审查；该模块已由 root 逐条独立读源，确认可数时间图、可测性、AE 换序及原时钟实例的正确性。它的最终字节与实际内核输出仍纳入本阶段整体绑定。

## 核对的数学内容

1. **真实过去，而非未来守卫。** 有限状态观测器从原历史纤维重建 chronological identity list 与实际标记，失败时回退初态；固定目标状态的纤维只作可数并。状态/联合/渐进可测性需要有限状态的地方明确带 Fintype，未对任意不可数状态作可数并。endpoint 本身使用原始 guarded word 的一次逆序和原身份标记，与 observer 的等值在共同样本满概率集上对所有时间成立；没有用 guarded endpoint 直接充当 adapted 过程。
2. **严格过去与当前分开。** beforeState 的有理左邻域图在真实 predictable σ 上可测，零时刻为初态。实际严格过去等式及单次事件更新在同一满概率样本集上对全部时间/事件成立，故能安全评价随机 ring。相反，before=current 的等式只在 Lebesgue 时间再原 law 的迭代 AE 意义下用于时间积分；没有代入随机 ring。其证明经原事件时间图零测，未假定当前状态共同可测或补偿等式。
3. **顺序、标记和符号。** 原 word 最新事件在前，实际执行恰好逆序一次。signed telescope 对每个 ring 使用原整个 horizon word 的 strict-past filter；Good 的严格时间次序排除事件冲突。逐标记 pathSum 重索引前先证明支持有限及有符号可和；pathwise 身份是原 z.2 e，未另采样或移位。正事件时间及同一全时刻 Good 集使任意 horizon 的 AE 陈述成立。
4. **先证明可积，再交换。** 任意有限状态实值 F 被 Σa‖F(a)‖ 控制，真实 predictable 增量绝对值至多两倍该界。由已有、真正原 law 的 bounded predictable compensation 得各 marked pathSum 可积，再得有限总和、实际观测量变化及时间均值可积，最后交换有符号积分/有限和。没有用 Lean 对不可积函数积分默认为零来得到假 Dynkin。
5. **率与实际状态。** 每原 site 的 false/true 贡献各带 1/2，生成元是逐 site 完整括号的 ((Ffalse+Ftrue)/2−F旧态)。生成元时间均值先可积，再经 time-first AE 替换为实际 current endpoint；physical time 为原 Real 的 (0,T]，不是更新次数或重标时间。旧态项没有误移到总和外。
6. **真实混合实例。** step 是原 MixedSquareModel.cellUpdate，endpoint_eq_mixed 为定义等值，保留相同 fallback、维度、事件身份及 law。原混合边界 NE=1/SW=0、形状不变性来自已验收模型；每个样本每个时刻的实际 current shape 满足 Monotone，故可用已证 corner/bond 生成元等式，得到每个列出 adjacent bond 交换率 1/2 的真实观测量 Dynkin。未以第三方过程定律或矩方程为输入。

## 明确限制

除状态无关的 null-graph 实例外，本阶段实际补偿仍沿原 DropletClockLaw 的 L 参数，即 ClockWordMarks.sample/measure(parameter L)，实际方格边长 2L+1。有限状态的泛型化没有凭空证明任意边长 clock restriction law。边长 8N+1 可作为后续放大候选，尚须真正跨尺寸联结。

当前结论是有界有限状态观测量的积分恒等式及必要可积性，不声称完整 SSEP 路径 law、热方程唯一性/微分方程、负相关、矩衰减、清除概率或二次恢复上界已经完成。下一实质任务是把 density/product observables 接出真实矩方程，再证明热衰减与异点协方差控制，并接跨尺寸支配、原同步比较与重启。原含∞首达和 exact-N 最坏期望的最终上界仍未闭合；已完成下界不受本阶段改变。

## 冻结源指纹

- `FiniteObservedClockState`: `741483bed39952b2bdc80de45c2a2af9754396e41712dffa8739cac4b9e38fc0`
- `ClockTimeNullGraph`: `27baf73463d709c9f66a8ebd0f5e570ac9e2ada0f999bea46da127091c2d32fd`
- `FiniteMachinePreState`: `7c25c9ed68e47435c266f98bd7f56ca623113bc0473c22c4ac3ea8f6ed068180`
- `MachineTraceTelescope`: `a88acd449adfea75ea45613e0ff5e0d65831b169fc9a90aa81285025116adbe3`
- `MachineEventScores`: `2b7a4bf17d34757d13b1d6cc1242a88300efd74346336ab7c1a382a5f014f961`
- `MachineClockDynkin`: `95308d00c4ee6c6117e23570ff0b7531cda2a03665dd5be5c5282b194bbe1693`
- `MachineClockGenerator`: `a5a1435f56e9f5454359f3a9afe9dbf04461b06dcaa96581326f7b480f654c1b`
- `MixedClockDynkin`: `6562734c23ac4da93d076f601a5888437dba88b8b5989d2c9ea09a3aed5692e2`
