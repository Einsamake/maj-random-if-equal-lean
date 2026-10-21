# 原历史的标准可预测σ及有限唯一性：独立核查

核查代理`/root/interval_mark_factor`。独立AI检查，不是人类专家认证。

## 这一步的含义

规定“每次响铃前能够使用哪些信息”，然后说明：只要两把有限测度在这些基本过去记录条件下都一致，它们对所有允许的记录也一致。

## 原文语义核对

generators用{0}×E0和Ioi(s)×Es，事件来自RationalProtectedExit.nnHistory；后者是原MarkedClockFiltration.history按NNReal重标，不是rightHistory。与mathlib标准Filtration.predictable的生成定义以rfl严格一致，未自选一个较小σ代数冒充全部可预测权。

π系统交集逐类检查：零点矩形交零点矩形仍在F0；混合交不可能非空，因为NNReal时刻非负；两个未来矩形交归到max(s,t)，两过去事件均经原F单调性提升到Fmax再交。可预测σ包含于ambient产品σ，由两类生成矩形的真正ambient可测性证明，方向正确。

trim_eq_of_rectangle_masses是一般有限测度唯一性工具，参数是零点矩形、未来矩形和univ质量等式；这些不是实际补偿已证明的声明。实际结论必须在后续模块用真实point/reference的已证矩形质量逐项实例化，不能把hfuture或huniv作为主结果的未证参数。有限测度trim在标准较小σ上比较，没有推导整个ambient产品测度相等。

## 验证绑定

正式源码与预审冻结指纹一致。已独立核对本阶段29项具名声明的源名、审计表和实际输出逐项同序；实际统一构建与标准Lean --trust=0专项均退出0，仅有三个标准公理，无新Lean警告。专项验收时间为2026-10-22 06:54:49；最终全工程统一已独立绑定：197正式源，其中189分析源2504公开辅助定理，另8核心源125定理及1模型，共2630实际公理输出与源码、打印表逐名逐序一致；全部源集/SHA匹配。分析真实重建与标准trust0审计均0；核心8源核旧验收指纹相同，本阶段未重编。详见[predictable-clock-sigma-independent-evidence.json](predictable-clock-sigma-independent-evidence.json)。完整主定理未完成。
