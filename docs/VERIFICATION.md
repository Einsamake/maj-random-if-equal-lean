# 验证记录

分析240个证明模块、3173条辅助定理、241份分析源；核心旧125条定理与1模型、8源仅回核指纹未重编。共249份正式源、3299项实际公理输出。最新分析统一构建及标准Lean --trust=0审计实际退出0（2026-10-26T06:32:55.327815+08:00），仅三个标准公理，零新增Lean警告。

分析使用Lean4.35.0-rc4与固定mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d；核心使用Lean4.35.0，本轮未重编核心而核对原八源及旧实际审计。缓存与依赖未重置。

本轮新增8模块80theorem/93named，先逐项专项构建及标准trust0审计，再真实全分析统一build和逐定理公理输出。独立脚本核全部源集/SHA、名字与顺序、专项日志及draft字节；仅Classical.choice、Quot.sound、propext。零新增Leanwarning，仅原batteries文档local-change提示。无sorry/admit、自定义公理、unsafe、native_decide或内核绕过。

实际一点/同时两点矩积分方程、正时间ODE、异点非正协方差与中心能量已证明。热衰减/集中概率、跨尺寸clock与完整二次上界仍未完成。AI复核不是人类专家认证；本地验收不表示远端CI。

[本阶段详细证据](../formal/PROGRESS_2026-10-26_MOMENTS_COVARIANCE.md) · [独立语义](../formal/audit/mixed-moments-independent-review.md) · [完整绑定](../formal/audit/mixed-moments-independent-final-binding-evidence.json) · [统一验收](../formal/audit/analysis-validation.json) · [读者进度](../STATUS.md)。
