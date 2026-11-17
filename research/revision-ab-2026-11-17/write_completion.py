from pathlib import Path
import json
R=Path(__file__).resolve().parent
d=json.loads((R/'validation.json').read_text(encoding='utf-8'));assert d['status']=='PASS'
text=r'''# 二次恢复定理：A/B 修订

本轮完成 A1–A3、B1–B3 的论文修订、原模型形式化接口与审计。研究对象仍为无限二维格点上的同步四邻多数规则，平票由独立公平标记决定；$N$ 是最小平移包围方形的边长，初态大小恰为 $N$，恢复时间允许取无穷。

论文见 [revision 6 PDF](paper/output/pdf/quadratic-recovery-v6.pdf)，可编辑正文见 [paper.md](paper/paper.md)。

| 任务 | 完成内容 | 原模型声明入口 |
|---|---|---|
| A1 | 强化下界完整进入摘要、主定理、几何证明与常数组装：$N\ge500001$ 时 $N^2/576000000\le\tau(N)\le664066N^2$ | `OriginalConsequences.quadratic_bounds`；两份旧强化依赖原样重编 |
| A2 | 对 $N\ge16$、任意允许初态和整数 $j\ge0$，明确统一几何块尾 $\mathbb P(T_x>jb_N)\le2^{-j}$ | `OriginalRecoveryResults.original_recovery_block_tail` |
| A3 | 将两处重复的物理时钟计算统一为有限状态可观测量引理，再分别实例化；保留公平标记、每点速率1及有限方形地点范围 | `OriginalConsequences.finite_machine_dynkin`；纸面§3.4 |
| B1 | 在扩展期望中证明填满方形实现极值：$\tau(N)=\mathbb ET_{\mathbf1_{Q_N}}$，$N\ge2$ | `OriginalRecoveryResults.tau_eq_full_square` |
| B2 | 准确失败率、条件重启、$a_N\le\min(1/2,5/N)$、$a_N\to0$及$\mathbb ET_x,\tau(N)\le b_N/(1-a_N)$ | `OriginalConsequences.original_sharp_block_tail`、`original_sharp_expectation`；`SharpRecoveryTail.tau_le`；`SharpFailureRate.failure_isBigO_inv` |
| B3 | 任意固定实数$r>0$的矩界与$0<\lambda<\log2/332033$的统一指数矩界；先由真实尾界排除正概率无限恢复 | `OriginalConsequences.original_rpow_le`、`original_exponential_lt_top` |

其中
$$
b_N=331776N^2+257,\qquad
a_N=\frac{32}{8N+1}+\frac{12}{5}N^2 2^{-(1296N^2+1)}.
$$
两个时间尺度的比较因子、调度误差及加性常数均保留。上述分布结论对所有允许的确定初态一致；正概率的二次下侧等待仍由填满方形这一慢见证提供。

## 验证

本轮重新编译原正式工程的267份项目源（259份分析源、8份核心源），并在其独立新缓存上重编5个新增模块和2份原样复制的强化下界依赖。新增模块有58个命名声明，其中52个定理、6个定义；统一公理审计另含旧强化依赖47项，共105项。全部使用标准 Lean `--trust=0`，公理输出仅含 `propext`、`Classical.choice`、`Quot.sound` 及其子集。锁定的外部 Lean/mathlib 依赖沿用已安装版本，本轮未重建这些外部库。

完整命令、实际日志、源与产物指纹见 [validation.json](validation.json)、[统一构建记录](evidence/unified-build.json) 和 [原工程重建记录](evidence/base-replay/replay.json)。独立AI数学及源码语义复核见 [审查记录](evidence/independent-source-review.md) 与 [最终运行绑定](evidence/independent-final-binding.json)。这是内部独立复核，未经过人类专家评审。用户于2026年11月17日明确取消本轮本科模拟读者验收。

PDF进行了原生双遍编译、全部页面渲染与版式核查，详见 [PDF记录](paper/review/pdf-validation.json)。原267份源、v5正文/TeX/PDF和原封存ZIP的字节保持不变。新成果保存在独立目录，未对外发布。

## 合作者后续

C1（文献定理与同步模型的短路线）和C2（一阶矩加原时钟重启的替代上界）留给合作者。本轮没有开展这两项候选；它们不构成已完成A/B结果的证明假设。具体任务与验收条件沿用 [交接清单](../../docs/collaborator-handoff-2026-11-14/TASKS.md)。

## 复现入口

`rebuild_base.py` 将两套固定版本项目源分别重编到独立缓存；`final_build.py` 等待其真实成功后，按依赖顺序构建新增模块，并生成逐命名声明的 `RevisionAxioms.lean`。脚本采用本项目本机D盘布局，产物写在脚本所在的新修订目录；外部合作者须按自己的检出和已安装工具调整项目根目录、Lean二进制位置，并先恢复锁定依赖。`validate_revision.py` 核对构建、复核、论文及封存输入的绑定，不能替代实际Lean执行。
'''
(R/'README.md').write_text(text,encoding='utf-8',newline='\n')
checkpoint='''# A/B 修订检查点

状态：complete；2026-11-17。

用户授权的A1–A3、B1–B3论文修订、原模型形式化和审计全部完成。C1/C2保留给合作者，不启动其他自由探索。

验收入口README.md与validation.json。267旧项目源已重新编译，5新模块58命名声明与2复制依赖47声明统一标准trust0审计，原模型law、exact-N、两背景和无穷值保留。锁定外部Lean/mathlib沿用现有安装，非外部库重建。独立AI源码/纸面复核完成；用户明确取消本科模拟读者验收。新PDF已真实编译、全部页面渲染及版式核查。旧267源、v5及ZIP冻结未改。

权威交付目录D:/MyWorks/Math/research/revision-ab-2026-11-17；C:/Users/Lenovo/Desktop/Project/Math/revision-ab-2026-11-17为本轮暂存及独立编译缓存。无需恢复证明进程。本轮单次额度计划应暂停，未对外发布、未提交arXiv、未联系他人。
'''
(R/'CHECKPOINT.md').write_text(checkpoint,encoding='utf-8',newline='\n')
print('README and complete checkpoint written after actual PASS')
