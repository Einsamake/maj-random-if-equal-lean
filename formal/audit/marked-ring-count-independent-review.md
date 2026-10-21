# 原历史中的实际响铃计数：独立审查

当前：正式模块20条定理、22个命名声明逐原文语义、正式源码SHA与全部专项输出已独立核对。专项实际build0、标准Lean --trust=0审计0，仅标准三公理，零新Lean warning。正式SHA256：`ec1099348fb11a093759362f97602b5be50c7755e874a32f9a1d9232ebe01385`。最终统一于 2026-10-21T20:46:21.454420+08:00 实际build0/标准trust0审计0；本代理逐项核完整183正式源集合及所有SHA、2371分析与126核心的全部2497项公理输出逐名逐序一致（含名称内撇号），并将四新模块50theorem/53named与统一源码绑定。核心沿用旧审计、8源SHA未变，未冒称本轮重编。独立AI检查不是人类专家认证；主定理尚未完成。

## 对读者的意义

现在能严格地定义并观察“到这一刻，这个格点响过多少次”和“其中多少次携带黑色或白色标记”。正常时钟路径在任何有限时刻都只响有限次；同批MarkedRingIntegrability另经实际概率求和证明平均次数有限，未把两者混为一谈。

## 定义与历史信息

count和markedCount均直接对实际identity(v,k)的到时≤t事件求ENNReal指示函数之和，不用把无限计数改成0的ncard或toReal。每个identity只数一次，零间隔坏路径同时到时也按identity分别计数。所有事件保留到时等于t的那一响。

count_history_measurable只使用原F_t中的arrival≤t事件。markedCount_history_measurable使用arrival≤t且该identity标记=b的联合已揭示事件，并没有把任意未来mark坐标当成F_t已知。环境可测性另独立证明，后续Tonelli的可测条件确实提供。

## 无穷、有限与平均值的边界

- 单调性、两种mark的计数分割、markedCount≤count均逐样本成立，包括∞；没有使用∞相减。
- 只有给定真正有限coverage集合，才把tsum转成该集合基数。有限性来自实际clock_locally_finite_ae，通过真实product measure的fst拉回；同一个全测集合同时覆盖所有site和所有实t，没有对不可数时间逐一取AE再错误相交。
- count_eq_top_of_all_arrived明确保留所有arrival均已到时时的∞。t=0计数为0只作AE声明，利用真实所有到时严格正；并不把坏路径逐样本清零。
- 两个lintegral-tsum恒等式是真正非负Tonelli，允许两边∞，不要求计数预先可积。
- 只看clock的到时事件等于clock事件×全部mark场，实际product measure及mark总质量1完成概率运输。由此count的非负积分等于真实clock到时概率级数；未假设或证明精确Poisson law、精确均值或条件补偿。

marked false/true的分解和积分恒等式为后续标记补偿准备接口，不宣称计数的未来增量与过去独立。AE路径有限不等于平均有限；本模块没有混淆这两者。

到时概率级数的可求和/有限平均已由同批后续模块真正证明；仍缺原F计数条件增量、更新前状态积分和真正物理Dynkin，之后还有边界修正累计控制及小岛收缩核心尾。主定理未完成。本审查不改Lean、不构建。
