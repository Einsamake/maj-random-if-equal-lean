# Verification

最新本地统一验证时间：2026-10-21T21:05:20.067211+08:00。分析2420条定理、180分析源；核心125定理及1模型、8源，本轮核对既有审计与8源指纹，未重编核心。所有正式源逐字节绑定对应audit JSON的SHA256，快照同步拒绝未验收或指纹漂移的正式源集。

分析使用Lean4.35.0-rc4与固定mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d；核心使用Lean4.35.0。从各自项目目录使用Lake构建，不跨工具链复用olean。formal/scripts/validate_analysis.py会真实统一build，再以标准Lean --trust=0审计每条分析定理；核心既有证据位于formal/audit/core-validation.json。

19日新增阶段专项由formal/scripts/audit_orthogonal_boundary_stage.py与formal/scripts/audit_stopped_clock_stage.py核验；后者覆盖命名instance。完整输出、源指纹和独立AI语义复核在formal/audit。仅标准Classical.choice、propext、Quot.sound，禁止占位、自定义公理、native_decide、unsafe和内核绕过。

本地batteries提示仅来自docs/README.md修改，未改证明或运行库；未上传该本地文档改动。没有声明GitHub远端CI完成。独立AI检查不等于人类专家认证；没有以欲证核心概率界为最终主定理参数。
