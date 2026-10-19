# 已验收合同：具体方形有限字 PW

2026-10-14 20:56:32 +08：以下合同已由实际源码、统一构建及全部公理审计完成，见 [阶段验收](PROGRESS_2026-10-14_PW.md)。此文件保留合同边界；当前下一阶段见 [NEXT_PHASE.md](../README.md)。

范围：实际 `SquareSpin.Config n`、固定零边界、`β≥0`、最大初态 `top := fun _ => true`、单调实测试函数 `φ`、时间正序字 `s.Sublist w`，允许重复站点。

## 最终必须交付

1. `ZeroTemperature.warmWord β w φ top ≤ ZeroTemperature.warmWord β s φ top`。
2. 用已有有限字极限推出 `actualMajorityWordMean w φ top ≤ actualMajorityWordMean s φ top`。
3. 对真实事件字 `W.Nodup`、`S.Sublist W`，通过 `FiniteWordKernel.chronological_fair_execution_mean` 得到实际公平积积分比较。`freshRun` 接受 newest-first，所以时间正序 `W` 传 `W.reverse`。

最终只接受 `β≥0`、测试函数单调、Sublist、身份无重复等结构条件，不把密度保持、删更新或 law 作为输入。只完成中间引理不能宣布 PW 阶段完成。

## 顺序

1. 实际热浴概率随配置单调，`warmStep` 保持单调实函数。
2. 定义有限实质量更新和 `ρ/πβ` 密度，以真实详细平衡证明更新密度等于 `warmStep`，进而保持单调。
3. 以布尔两点纤维非负差乘积证明单步降低随机序。
4. 最大态 Dirac 密度单调；前缀归纳、后缀传播及 Sublist 归纳得到最终有限字不等式。
5. 零温及公平标记实际积分连接。

参考 [Peres–Winkler §2](https://arxiv.org/html/1112.0603)。无需一般自旋、硬约束、total variation 或 PMF 包装。

## 验收与边界

新模块单独及统一构建、全部新增公开定理公理审计、禁用构造扫描及哈希通过。无占位、自定义公理或内核绕过。全称声明覆盖空字、相等字及同站点重复。

范围止于确定有限字实际积分。随机时钟纤维平均、完整扫描 Sublist、恢复事件、CMST／FSS、实际重启及期望另验收。不把分布比较写成同标记逐样本不等式，不扩张到任意初态。
