# 条件计数阶段：独立语义及已有内核证据核查

复核代理：`/root/interval_mark_factor`。这是独立AI检查，不是人类专家认证。本文独立核查他人编写的 ClockIntervalCount、ClockIntervalHistory 和 MarkedConditionalCount；本代理自己的 MarkedIntervalFactor 留给根代理及另一代理核查，不作自我独立认证。

## 先说明这两步解决什么

要累计一段时间里的更新，必须数清“观察以后、截止以前”的响铃，并且允许此前看到的记录影响观察条件。第一模块定义这段区间的实际次数；第二模块说明，对任一固定等待段，在任意过去记录条件下，它贡献的平均等待长度仍等于该次响铃在区间内发生的概率。这还不是整个小岛的消退时间界。

## 区间计数：无穷不能被减掉

[ClockIntervalCount](../drafts/ClockIntervalCount.lean) 用逐identity指示函数的非负级数定义(s,t]计数，异常路径上无穷仍为∞。左端严格排除、右端包含，恰好使count(s)+interval(s,t)=count(t)在s≤t时逐点成立；没有先写∞-∞。可测性使用原截止t历史里的arrival≤s和arrival≤t事件，没有观察未来标记。

有限平均来自interval≤count(t)及既有真实总计数期望上界，随后才取得Real代表可积。Real差公式另在真实共同AE有限集合上从加法恒等式推出；没有把“每条正常路径次数有限”当成平均有限。Tonelli形式保留非负扩展积分，可对任意限制测度使用。

等待段占用差逐点非负；已在s以前结束的段贡献差为零。有限和用两次真实占用望远镜之差，达到t以后所有段都为零，于是非负无穷级数等于t-s。只使用一个真实全site趋于无穷的AE集合来同时覆盖全部实s,t，没有对不可数个AE事件直接相交。原clock/mark产品测度下的共同AE结论由真实fst准保测映射运输。

## 局部消去历史指示：只在仍有贡献的支撑上

[ClockIntervalHistory](../drafts/ClockIntervalHistory.lean) 首先证明确定前缀p的截断占用差公式。它用已证真实cap积分，再以有限非负积分的差得到arrival∈(s,t]概率。s≤t保占用单调；减去的cap积分先证明有限。对所有实p,s,t和原始负gap均成立；prior>s的分支由真实prior-cap公式内已处理的零/空事件覆盖，不将其错误改成gap≤0事件。

重要的可复用方法是：若当前identity在s以后才到，重置其gap到s以后，原历史事件E保持；这把E的指标改成仅依赖其它坐标的指标。若当前identity已在s以前到，重置未必保E，但该段占用差已经逐点为零，因此指标不变性不再需要。消去历史仅在被积函数非零的支撑上进行。

随后使用真实独立gap与其余全部坐标的产品分布逐fiber积分。没有声称reset映射保持概率分布，没有把随机cutoff直接套进固定截断law，也没有引入Poisson计数、条件均值或补偿公式作为前提。结论仅为固定identity、原common clock历史事件的占用/窗口质量恒等式；搬回原joint marked历史与对所有identity求和仍由后续模块承担。

## 当前证据边界

ClockIntervalCount 18条定理/19项命名声明，冻结SHA `06e16194a2eb24b3fcc9a695ea15cb3ff793fc36715e8c1800d2798eafa0f8ba`；ClockIntervalHistory 5条定理/6项声明，SHA `2c98e9461c7321981cf072f55e01dabd29fa5ef8851a13cf4d6771525e70332d`。两个草稿实际标准Lean --trust=0日志退出0，源码与记录、所有列出的正式依赖SHA已独立核对，零新增Leanwarning，仅既有batteries文档local-change提示。

最新正式专项43项声明的源码表、打印表和实际输出已全部逐名逐序核对（含本代理factor3项的机械证据，语义独立认证仍由他人负责）；其中他人编写的count/history/conditional三模块共37定理/40项正式声明与原审草稿SHA相同。2026-10-22T01:53:06.434252+08:00的build0、标准trust0公理审计0、三标准公理和零新增Leanwarning均已实际核对。最终194源全局统一已独立完整核过：2480分析+126核心共2606项公开公理输出逐名逐序含撇号，全部源集和SHA一致；core8旧源未重编。核查者未修改这两个Lean源、未启动它们的构建。详见[机器核查记录](conditional-clock-independent-evidence.json)。完整主定理未完成。

## 原联合历史下的最终条件均值

MarkedConditionalCount的14条定理及1定义已逐原文复核，正式冻结SHA `acddadaf3cff37550c1a0901aef2997712cd73ff420855352287578e501766b3`。它先固定整个标记字段；原过去事件E的每个固定标记section仍在原clockHistory中可测，由已证真实section定理保证。真实clock×mark产品测度上的Tonelli把固定gap恒等式搬回原jointF，并没有把E与未来标记独立当成前提。

对所有identity的占用增量作非负Tonelli求和，在限制E的测度下沿真实共同AE集合得总和t-s，因此窗口计数积分=(t-s)μ(E)。E可以概率0，全程不除μ(E)。Real差等式只在既有AE有限性下识别原count(t).toReal-count(s).toReal。原有∞定义不被改变，区间的Real代表及原总计数代表可积。

标记窗口另按固定尚未揭示identity的公平翻转因子逐项相加，得到各色预配标记的条件平均为(t-s)μ(E)/2。它不表示实际把格点改黑/改白各一半；多数票确定时标记可能不影响更新。结果只识别原历史下的条件均值，没有给整个未来向量或条件分布的强Markov结论，更未提供可预测面积补偿或CMST/FSS时间界。

## 最终统一绑定

2026-10-22T02:01:03.158845+08:00实际analysis build0/标准trust0 audit0。194正式源，2480分析公开定理加125核心定理及1模型，共2606项公理输出逐名逐序与源码公开声明表和打印表匹配（含撇号）；各新模块SHA与正式专项及全局记录相同。只见标准三公理、零新warning；核心8源仅核旧审计与指纹，未重编。公开计数不把私有源码helper另计，但全源码同样扫描禁止构造，私有依赖由实际内核检查。见[最终绑定记录](conditional-clock-final-binding-independent-evidence.json)。本轮报告冻结；完整主定理未完成，非人类专家认证。
