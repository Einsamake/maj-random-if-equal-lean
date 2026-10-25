"""Update human documentation only from the actual accepted synchronous lower audit."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2]
a=json.loads((R/'formal/audit/analysis-validation.json').read_text(encoding='utf8'))
assert a['build_exit']==a['axiom_audit_exit']==0 and a['public_theorems']==2826
for name,h in a['source_sha256'].items():
    assert hashlib.sha256((R/'formal/analysis'/name).read_bytes()).hexdigest()==h
summary=("分析212个证明模块、2826条辅助定理、213份分析源；核心125条定理及1模型、8源未变。"
 "合计221份正式源、2951条辅助定理与1个模型，完整公理输出2952项。"
 f"最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（{a['validated_at']}）；"
 "仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，本次未重编核心。")
for rel in ['docs/VERIFICATION.md','formal/LEAN_README.md','formal/FORMALIZATION_MAP.md']:
    p=R/rel;s=p.read_text(encoding='utf-8-sig')
    s=re.sub(r'分析208个证明模块、2800条辅助定理.*?本次未重编核心。',summary,s,count=1,flags=re.S)
    if rel=='docs/VERIFICATION.md':
        s=s.replace('核心缺口是禁止birth与cleanup累计量、真实几何收缩概率和最终两向恢复界，不是把这些概率结论当最终假设。',
          '原同步exact-N二次期望下界已经核验；核心剩余是二次上界所需的真实慢过程比较和收缩概率。')
    if rel=='formal/FORMALIZATION_MAP.md':
        s=s.replace('profile和最大值已定义/对应；一般有限与二次界未证','profile和最大值已定义/对应；二次下界已证，一般有限和二次上界未证')
        s=s.replace('真实masked/expanded weighted raw严格相等，未得weighted整体漂移界','真实masked/expanded weighted raw严格相等；真实整体weighted率及下界见后续')
        s=s.replace('| 原同步二次上下界 | 尚未闭合 | 已有CLOCK结论到同步/原exact-N的数值接续、FSS上界自含核心及最终常数仍待 |',
          '| 原同步exact-N二次下界 | SyncLowerScale、ExtendedTailLower、SynchronousQuadraticTail、OriginalQuadraticLower | 真同步尾≥1/4、奇偶N支持比较、保∞期望；N≥786432000时ofReal(N²/56623104000)≤tau(N) |\n| 原同步二次上界 | 尚未闭合 | 有限混合边界/SSEP候选核心、真实概率与clock/sync上界连接仍待 |')
    s+='\n[25日：原同步与exact-N二次期望下界](%sPROGRESS_2026-10-25_SYNC_LOWER.md)。这只完成Θ定理的下界。\n'%('../formal/' if rel.startswith('docs/') else '')
    p.write_text(s,encoding='utf8')
p=R/'README.md';s=p.read_text(encoding='utf-8-sig')
start=s.index('## 现在证明到了哪里？');end=s.index('## 怎样核查这些成果？')
section="""## 现在证明到了哪里？

**已经完成主定理的下界：确实存在需要平方量级时间才能恢复的图形。** 对所有足够大的边长 N，初态取一整块 N×N 黑色方块，它的平均恢复时间至少是 cN²，其中 c 是一个与 N 无关的正数。

这是原题中所有格子同步更新的结论。证明保留了永不恢复时的无穷值，也处理了边长的奇偶；完整主定理还差二次上界。

下界是怎样得到的？我们先给辅助时钟过程中的黑格记分：靠外的格子分值低，某些难处理的边界变化恰好发生在零分位置。然后严格计算平均失分速度，证明图形没有足够时间失去保护。最后，用已经证明的更新方式比较，把这个结论接回原同步过程：经过平方量级的轮数，方块仍至少有四分之一概率没有恢复。这个概率就给出了平均时间的下界。

**现在要补的是另一半：保证任何同尺寸图形的平均恢复时间都不超过 CN²。** 我们正在研究一个边界呈阶梯形的辅助过程，把它的变化转成一条线上粒子的交换，以便控制恢复时间。这条上界路线仍在证明中。

| 证明部分 | 当前状态 |
| --- | --- |
| 原规则、尺寸、真实随机分布和含无穷的恢复时间 | 已核验 |
| 至少有一种图形，平均恢复时间达到 cN² | **已核验：原同步、恰 N 尺寸的二次下界** |
| 所有同尺寸图形，平均恢复时间不超过 CN² | 尚未完成 |
| 合并得到 τ(N)=Θ(N²) | 尚未完成 |

"""
s=s[:start]+section+s[end:];p.write_text(s,encoding='utf8')
(R/'STATUS.md').write_text("""# 当前进度：原同步模型的二次下界已证明

完整目标是 τ(N)=Θ(N²)，目前已经完成其中的下界，二次上界仍未完成。

## 这意味着什么

从一整块 N×N 黑色方块出发，所有格子按原规则同时更新。我们已经严格证明：对所有足够大的 N，它的平均恢复时间至少是 cN²，c 是一个固定正数。

关键概率结论是：经过一段与 N² 成正比的轮数后，仍至少有四分之一概率没有恢复。只要这部分随机结果还要继续等待，平均恢复时间就不可能太短。

这覆盖原无限方格、真实独立硬币、边长的奇偶、黑白背景互换以及尺寸恰好为 N 的最坏扩展期望。若某条随机路径永不恢复，仍按无穷计算。

## 还缺什么

现在必须证明另一半：所有允许的同尺寸初态，平均恢复时间都至多是 CN²。现有的重启工具可以重复一个成功概率界，但不能替代这个尚待证明的界。

下一条候选路线是用较大方框和混合边界构造较慢过程，把始终呈阶梯状的边界转成有限一维粒子交换。真实更新比较、编码和概率估计仍须逐步证明。

## 怎样验证

最新221份正式源已完成统一构建及标准Lean内核公理审计。独立AI审查与源指纹绑定另有记录；AI审查不等于人类专家认证。

<details>
<summary>显式常数与技术证据</summary>

当 N≥786432000 时，已经证明 τ(N)≥N²/56623104000。常数和阈值十分保守，只用于严格建立渐近下界，没有优化。

最终声明是 OriginalQuadraticLower.tau_quadratic_lower_bound 和 exists_positive_quadratic_lower，最终参数只有尺寸及其下限，没有所需概率或漂移界。

</details>

[从3×3例子理解问题](README.md) · [本阶段结果与验证](formal/PROGRESS_2026-10-25_SYNC_LOWER.md) · [源码与核验记录](docs/VERIFICATION.md)
""",encoding='utf8')
(R/'formal/PROGRESS_2026-10-25_SYNC_LOWER.md').write_text(r"""# 原同步、原exact-N二次期望下界

主定理的下界现在已经实际核验；二次上界和完整Θ仍未完成。

## 严格数学结果

对每个 N≥786432000：

$$
\operatorname{ofReal}(N^2/56623104000)\le\tau(N).
$$

τ 是原无限二维同步四邻规则下、尺寸恰N、到两种齐次背景的最坏扩展期望。∞仍保留。具体初态是N×N全黑方块，故这是最坏期望下界，不是每个图形的恢复时间下界。

SyncLowerScale令q=⌊L²/196608000⌋、k=q−1，证明k≥L²/393216000、调度时长≤L²/12288000和真实调度误差≤1/4。SynchronousQuadraticTail直接用已证真实物理均值界控制早时刻，并从同一clock law可测灭绝事件的补集得到生存≥1/2；实际two_way_clock_tail第一方向给原同步尾≥1/4。

ExtendedTailLower把常数尾集指示函数直接放入ENat.toENNReal非负扩展积分，给kP(T>k)≤E[T]，不要求T有限或可积。OriginalQuadraticLower取L=⌊(N−1)/2⌋，用同一N方框支持比较处理奇偶，再对两背景首达及exact-N优化供上述结论。最终模型定理没有核心概率或漂移作为输入。

## 实际验收

"""+summary+"""

本批4模块26theorem/29named：scale11、connection6、profile12三个专项实际build0及标准trust0审计0，零新Lean warning。旧217完整JSON、build、axiom输出和入口表归档before-sync-lower-stage-2026-10-25，不拿旧验收覆盖新源。

[独立语义审查](audit/sync-lower-independent-review.md) · [221源完整绑定](audit/sync-lower-independent-final-binding-evidence.json) · [统一核验](audit/analysis-validation.json) · [最终定理源码](analysis/MathResearchAnalysis/OriginalQuadraticLower.lean)。

独立AI不是人类专家认证；本阶段不证明任何原同步二次上界，也未优化巨大常数。

## 下一步

构建南/西白、北/东黑的有限混合边界过程，证明真实单点更新与下方闭合白色区域的阶梯边界对应，再推进有限SSEP的一、二矩和收缩概率。该上界路线仍待形式化，不能以已有下界或重启工具代替。
""",encoding='utf8')
p=R/'research/followup/METHOD_LEDGER_2026-10-25.md';s=p.read_text(encoding='utf8')
s=s.replace('原同步时间、原exact-N期望下界和另一条二次上界仍待；完整主定理未完成。','原同步时间与原exact-N二次期望下界现已接通，见下面续记；另一条二次上界仍待，完整主定理未完成。')
s+='''

## 续记：先运送尾概率，再取扩展期望

直接使用已存在的第一方向clock/grid比较，将时钟生存≥1/2扣去真正调度误差≤1/4，得到原同步尾≥1/4。对早时刻重新使用一般时间均值界，避免为此单独重建整条clock CDF单调性。

奇偶尺寸通过“把较小奇数实心方块放进原N方框”处理，使用真实支持比较，不先引入新的τ单调命题。尾集常数指示函数直接积分ENat.toENNReal，完整保留∞。最终原exact-N二次下界只有尺寸假设：[实际结果](../../formal/PROGRESS_2026-10-25_SYNC_LOWER.md)。

## 上界候选：有限混合边界与有限粒子

可尝试在较大M×M方框设西/南0、北/东1，让白色集合始终向西南闭合。边界可编码为2M步路径，每个可翻角对应相邻01/10交换，真实翻转率为1/2。路径中点(J,J)给原N方块全白的条件J≥N。

这可把上界核心缩成有限SSEP的热能耗散与二点负协方差，不必为只需常成功概率的目标证明更强的无限系统指数尾。所有边界、编码、原law比较、生成元与概率估计仍须真实证明；此处记录的是候选路线，不是已完成上界，也不声称方法全球新颖。
'''
p.write_text(s,encoding='utf8')
# Curate all new named audits and later mixed-boundary evidence in all three material tools.
for rel in ['scripts/validate_workspace.py','formal/scripts/package_lean.py','scripts/sync_private_repository.py']:
    p=R/rel;s=p.read_text(encoding='utf-8-sig')
    s=s.replace("'physical-weighted-*',","'physical-weighted-*', 'sync-lower-*', 'mixed-square-*',")
    p.write_text(s,encoding='utf8')
print('Updated human docs from actual 221-source accepted audit; independent review links awaiting final binding.')


