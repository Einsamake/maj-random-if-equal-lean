# 真实逐次响铃的可预测补偿：独立核查

核查代理`/root/interval_mark_factor`。独立AI检查，不是人类专家认证。

## 这一步的含义

给每次真实响铃附一个只由铃前信息决定的非负数，把这些数逐次相加后取平均，等于把每单位时间的平均贡献按速率一半连续累积。这一半对应某一预配公平标记；不表示实际改黑或改白各一半。

## 实际假设和范围

trim_eq_reference真正实例化前阶段actual点测度的零/未来矩形质量，以及本阶段真实Lebesgue参考测度的矩形和总质量。最终定理的参数只有原L/v/b和有限T，没有把Poisson、补偿或核心收缩概率作为输入。

两测度只在原nnHistory的标准predictable σ上trim相等。对f要求在该σ下可测，先以lintegral_trim从ambient积分移入trim，替换测度，再移回；提升hf.mono仅把已知predictable可测性变成ambient可测，绝未反向。任意仅ambient可测、可能使用未来信息的f不被包括。

非负pathwise公式返回原ClockWordMarks下各实际identity窗口指示的可数和，保持原事件时间与完整样本，允许和及积分∞。参考侧是真Real Lebesgue(0,T]积分与原μ期望，系数1/2来自真实marked intensity，不是外加时钟过程。

另有Real Bochner积分的测度间等式；无可积时其总定义可为零，不能自动读成有限期望。源码因此另证明实际两测度下可积性等价，以及有界可预测Real权在两边确实可积。它仍未给实际signed逐路径面积和的Dynkin公式，也没有证明实际更新前状态已经可预测。

实际pre-event状态、mask禁止出生的累计修正、自含CMST/FSS核心尾和τ(N)=Θ(N²)主定理仍缺。本阶段补偿对抽象但真实可预测的权成立，不能跳过实际面积权的接口证明。

## 验证绑定

正式源码与预审冻结指纹一致。已独立核对本阶段29项具名声明的源名、审计表和实际输出逐项同序；实际统一构建与标准Lean --trust=0专项均退出0，仅有三个标准公理，无新Lean警告。专项验收时间为2026-10-22 06:54:49；最终全工程统一已独立绑定：197正式源，其中189分析源2504公开辅助定理，另8核心源125定理及1模型，共2630实际公理输出与源码、打印表逐名逐序一致；全部源集/SHA匹配。分析真实重建与标准trust0审计均0；核心8源核旧验收指纹相同，本阶段未重编。详见[marked-predictable-compensation-independent-evidence.json](marked-predictable-compensation-independent-evidence.json)。完整主定理未完成。
