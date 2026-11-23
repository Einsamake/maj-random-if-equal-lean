# 研究资料

[English](README.md) · [项目首页](../README.zh-CN.md) · [Lean 与审计](../formal/README.zh-CN.md)

## 同步四邻多数规则

每轮所有格点同时取上一轮四个最近邻的多数，平票由各格点、各轮次相互独立的公平硬币决定。$N$ 是包含有限扰动的最小平移轴平行方形边长，按格点数计。$\tau(N)$ 是两种背景上、尺寸恰为 $N$ 的所有确定初态的最坏扩展期望恢复时间，永不恢复时记为无穷。记 $T_N$ 为从白底全黑 $N\times N$ 方形出发首次恢复全白的时间。

| 研究 | 文章与验证 |
| --- | --- |
| 2026 年 11 月 19 日。对每个 $N\ge1$，$\tau(N)\ge\mathbb E[T_N]\ge\max\{m_N,N^2/850000\}$，其中最早恢复轮数 $m_N$ 为奇数边长时的 $N$、偶数边长时的 $N-1$。每条轨迹均满足 $T_N\ge m_N$，最早恢复的概率严格为正。 | [最早消亡及概率](lower-bounds-2026-11-19/earliest.md) · [早消亡概率与渐近系数](lower-bounds-2026-11-19/lower-tail.md) · [验证记录](lower-bounds-2026-11-19/evidence/validation.json) |
| 2026 年 11 月 18 日。先证得全尺度下界 $\tau(N)\ge\mathbb E[T_N]\ge\max\{N/2,N^2/1900000\}$，并给出全占据方形的过早恢复概率上界。 | [研究说明](lower-bounds-2026-11-18/README.md) · [证明笔记](lower-bounds-2026-11-18/lower-bound.md) · [验证记录](lower-bounds-2026-11-18/evidence/validation.json) |
| 第六版英文工作稿及 A/B 修订。原同步过程的二次恢复定理、满方形极值、统一块尾、保留失败率及矩估计。 | [英文 PDF](revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) · [英文 Markdown](revision-ab-2026-11-17/paper/paper.md) · [A/B 修订说明](revision-ab-2026-11-17/README.md) |
| C1 与 C2。C1 以连续时钟文献界为输入，推出同步二次界。C2 以一阶矩和确定时刻重启给出替代上界。 | [英文 C1](manuscript/quadratic-recovery-v6/C1-clock-literature.md) · [英文 C2](manuscript/quadratic-recovery-v6/C2-first-moment-upper.md) · [英文验证记录](manuscript/quadratic-recovery-v6/C1-C2-verification.md) |

## 随机等待网络

[总览](exploration/README.md)给出有向网络的解比较、三节点等待时间的概率表示、各参数的比较和辨识。公开材料从[顺序保持原理](exploration/NETWORK_PROOF.md)延伸到[第 12 阶段](exploration/phase12/README.md)的观测比较。

在该阶段的算例中，先等概率选定一个模型，再在给定模型后独立生成 100 次任务。仅使用完成时间的任意可测确定性规则，平均成功率至多 $353/606$。使用实际分支标记的一条固定阈值规则，平均成功率至少 $33/50$。因此两者的成功率相差至少约 7.75 个百分点。[第 12 阶段验证记录](exploration/phase12/validation.json)
