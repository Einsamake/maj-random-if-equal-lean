# 版本状态

截至 2026 年 11 月 20 日，仓库已收录原二次恢复定理、A/B 修订以及[全占据方形的最早消亡与强化下界](research/lower-bounds-2026-11-19/earliest.md)。当前论文为 [revision 6（60 页）](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf)，数学结果与源码入口见[研究结果](docs/RESEARCH_RESULTS.md)。

## 二维随机多数规则

原同步四邻公平平票规则满足

$$
N^2/850000\le\tau(N)\le664066N^2\qquad(N\ge16).
$$

下界对每个 $N\ge1$ 成立。11 月 19 日的结果以独立研究补充收入仓库；下列 revision 6 PDF 保留其原有常数。$N$ 为最小平移轴平行包围方形的边长，最坏期望在尺寸恰为 $N$ 的确定初态及两种背景上取值。修订还给出填满方形的极值等式、保留失败率的块尾、任意固定正阶矩及统一指数矩。相关量词和常数见[当前结果](docs/RESEARCH_RESULTS.md)。

原 2026-10-26 定理与 267 份正式源保持原版本，其下界为 $N^2/56623104000$，门槛为 $786432000$。强化下界先在独立 phase2 中证明，现已纳入 revision 6；新增的原模型结论位于独立的 [A/B 修订目录](research/revision-ab-2026-11-17/README.md)。11 月 17 日的验收重编了 267 份项目源，并审计了新增模块与强化下界依赖，详见[验证方法](docs/VERIFICATION.md)。

revision 6 为已收入 GitHub 的工作稿。其目录内的 README、检查点及运行记录保留发布前验收时的字节，因此其中“本地”“未发布”等措辞属于该历史快照；后续发布由 [PR #6](https://github.com/Einsamake/maj-random-if-equal-lean/pull/6) 及[发布记录](docs/ab-publication-2026-11-17/publication.json)标识。合作者的 C1、C2 替代路线已由 [PR #9](https://github.com/Einsamake/maj-random-if-equal-lean/pull/9) 合入，见[相应版本的验证说明](research/manuscript/quadratic-recovery-v6/C1-C2-verification.md)。

## 等待网络与公开范围

等待网络的公开材料覆盖至 [phase12](research/exploration/phase12/validation.json)，包含随机等待表示、参数比较、完成时间辨识界及路线标记规则。定理条件见[研究结果](docs/RESEARCH_RESULTS.md#随机等待网络)，文件入口见[等待网络目录](research/exploration/README.md)。本地 phase13–phase19A 的源码及数据未收入此公开版本。

本次首页和配套说明修订不改变数学源、论文快照或封存包，也不产生新的 Lean 构建记录。现行文档检查与独立模拟数学读者复核记录位于 [docs/mathematical-introduction-2026-11-17/](docs/mathematical-introduction-2026-11-17/README.md)。
