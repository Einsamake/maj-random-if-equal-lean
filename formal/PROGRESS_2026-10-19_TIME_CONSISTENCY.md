# 跨物理时刻的真实字与冻结路径

新增ClockWordConsistency模块20条定理及20命名声明。专项及统一标准trust0真实通过，已去掉1条不改变目标的noop后重新核验；当前源零新Leanwarning。该阶段历史统一为2129分析定理、156分析源/164全部正式源。

1. 严格递增时序列表的阈值filter是前缀。真实reverse clockword(s)恰为reverse clockword(t)按时刻≤s的filter，s≤t时为真实前缀，不仅子序列或相同事件集合。
2. markedEvents只反转一次且保留原identity mark。stoppedWord_append接出同一随机样本下的跨t执行一致性；首次loss后永久冻结，loss事件measure单调。
3. 直接复用既有ClockEventWord.good_ae的AE样本上∀实t共同Good，再经真实product measure的fst准保测映射lift。没有把∀t AE误换成AE∀t。正clockgaps给真实物理初态stateAt(0)=S。
4. 从(t+1)之前有限真实事件取严格大于t的最小future time；若无future事件取t+1。得到真正b>t且[t,b)无新事件。ring恰在t已计入。对同一AE样本的所有实t，word和实际stateAt都在[t,b)常值。

[正式源码](analysis/MathResearchAnalysis/ClockWordConsistency.lean) · [20named专项](audit/clock-word-consistency-stage-declarations-validation.json) · [独立AI](audit/clock-word-consistency-independent-review.md)

右侧局部常值已证明；本阶段尚未给滤过意义的IsStoppingTime、可测选b、强马氏或生成元/补偿。随后[物理首失守阶段](PROGRESS_2026-10-19_PHYSICAL_EXIT.md)将使用这些路径性质，不把它们当概率尾假设。
