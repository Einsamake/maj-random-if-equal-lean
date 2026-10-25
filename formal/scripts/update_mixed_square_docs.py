"""Refresh current human progress after the actual mixed-boundary whole audit."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2]
a=json.loads((R/'formal/audit/analysis-validation.json').read_text(encoding='utf8'))
assert a['build_exit']==a['axiom_audit_exit']==0 and a['public_theorems']==2878 and a['project_lean_files']==216
for rel,h in a['source_sha256'].items():
    assert hashlib.sha256((R/'formal/analysis'/rel).read_bytes()).hexdigest()==h
summary=("分析215个证明模块、2878条辅助定理、216份分析源；核心125条定理及1模型、8源未变。"
 "合计224份正式源、3003条辅助定理与1个模型，完整公理输出3004项。"
 f"最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（{a['validated_at']}）；"
 "仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，本次未重编核心。")
for rel in ['docs/VERIFICATION.md','formal/LEAN_README.md','formal/FORMALIZATION_MAP.md']:
    p=R/rel;s=p.read_text(encoding='utf-8-sig')
    s=re.sub(r'分析212个证明模块、2826条辅助定理.*?本次未重编核心。',summary,s,count=1,flags=re.S)
    if rel.endswith('FORMALIZATION_MAP.md'):
        s=s.replace('| 原同步二次上界 | 尚未闭合 |',
          '| 上界辅助模型与真实同维clock基础 | MixedSquareModel、MixedSquareCorners、MixedSquareClockLaw | 真实混合边界、精确双向翻角、空间单调形状保持、同clock/mark endpoint可测及原同维支配；非跨尺寸law或SSEP概率 |\n| 原同步二次上界 | 尚未闭合 |')
    s+='\n[25日：混合边界与真实阶梯形clock基础](%sPROGRESS_2026-10-25_MIXED_BOUNDARY.md)。这部分尚不给恢复时间上界。\n'%('../formal/' if rel.startswith('docs/') else '')
    p.write_text(s,encoding='utf8')
p=R/'README.md';s=p.read_text(encoding='utf8')
s=s.replace('我们正在研究一个边界呈阶梯形的辅助过程，把它的变化转成一条线上粒子的交换，以便控制恢复时间。这条上界路线仍在证明中。',
 '我们已证明一个辅助过程在真实响铃更新下始终保持阶梯形边界，并且在相同区域内保留的黑格总能覆盖原过程。下一步把这条阶梯转成一条线上粒子的交换，再估计它移动的速度。恢复时间上界仍在证明中。')
p.write_text(s,encoding='utf8')
p=R/'STATUS.md';s=p.read_text(encoding='utf8').replace('最新221份正式源','最新224份正式源')
s=s.replace('真实更新比较、编码和概率估计仍须逐步证明。',
 '目前已核验真实混合边界更新、阶梯形状保持，以及相同区域内使用原时钟和硬币的比较。不同区域的时钟对应、粒子编码和概率估计仍须逐步证明。')
s+='\n[已核验的上界辅助模型基础](formal/PROGRESS_2026-10-25_MIXED_BOUNDARY.md)。\n';p.write_text(s,encoding='utf8')
(R/'formal/PROGRESS_2026-10-25_MIXED_BOUNDARY.md').write_text("""# 上界准备：真实混合边界与阶梯形状

原同步exact-N二次下界已完成，完整二次上界与Θ仍未完成。本阶段建立上界候选辅助过程的真实确定性与同维时钟基础，不证明其恢复概率。

## 严格完成的内容

MixedSquareModel在现有有限边长n+2上定义实际混合边界：西/南外部0、北/东外部1，交角由负坐标优先0。内部四邻不读对角交点。沿用原四输入majority、排中心和真实tie mark；原zero-boundary同尺寸单点更新在同mark下不超过mixed更新。

MixedSquareCorners证明空间Monotone（白色SW downset）的精确翻转分类：1变0恰须南/西0且tie=false；0变1恰须北/东1且tie=true。真实单点写入及任意有限identity-mark事件词保持形状；两个方向均保留，未将过程改为永久擦除。

MixedSquareClockLaw直接使用原ClockEventWord.word的逆序和原identity-indexed标记z.2，异常空字fallback相同。有限vector只用于可测重构，不重新抽样，也不宣称重复身份时独立fresh law。实际endpoint可测；原zero-boundary与mixed整词逐样本支配给真实同维nonzero概率比较；从全1起，所有样本、所有实数时刻的endpoint都保空间Monotone。这个形状结论不宣称旧globally-guarded word对原历史逐样本适应。

## 未完成的内容

这只比较相同有限区域，没有原N区域到更大M区域的clock限制law；没有完整SSEP编码、条件flip率生成元、一二矩ODE、Poincare或协方差概率界。mixed全0也会从NE边界重新生1，因此不能把它当吸收态或调用原恢复时间restart。

下一阶段推荐用实际每行白格数λ_y和p_r=r+λ_(r.rev)编码有限粒子。右半粒子数J应等于白色对角格数，核心接口f(d,d)=false iff d.val<J避免N−1截断减法。有关接口仍是下一阶段待证计划。

## 实际验收

"""+summary+"""

本批3模块52条新定理、63项命名声明，三个专项分别32、18、13named均实际build0及标准trust0审计0，零新Leanwarning。旧221完整JSON/build/输出/入口和表存audit/history/before-mixed-square-stage-2026-10-25；下界4模块数学源未改。

[独立语义审查](audit/mixed-square-independent-review.md) · [224源完整绑定](audit/mixed-square-independent-final-binding-evidence.json) · [统一核验](audit/analysis-validation.json) · [真实时钟接口源码](analysis/MathResearchAnalysis/MixedSquareClockLaw.lean)。

独立AI不是人类专家认证。没有sorry/admit、自定义公理、native_decide、unsafe或内核绕过；没有把想证的核心上界当最终参数。
""",encoding='utf8')
p=R/'research/followup/METHOD_LEDGER_2026-10-25.md';s=p.read_text(encoding='utf8')
s+="""

## 续记：保留双向翻转，把形状直接接到原时钟

现已核验真实混合边界规则、精确corner翻转和阶梯形保持。比较用同一identity word与同一mark逐次传递，再放回原ClockWordMarks.measure，得到同维真实endpoint概率支配；没有凭画图或形式生成元替代过程。

实际field的finite-vector重构只为可测性，不用于重抽mark或宣称重复身份独立；所有样本的形状保持也不意味着旧全局guarded word逐样本适应。mixed全0非吸收，下一步只估固定时刻目标子块是否全0，不能照搬原吸收恢复时间。

[阶段核验](../../formal/PROGRESS_2026-10-25_MIXED_BOUNDARY.md) · [待证有限SSEP路线](UPPER_FINITE_SEP_ROUTE_2026-10-25.md) · [下一阶段行长编码接口](YOUNG_PROFILE_PLAN_2026-10-25.md)。
"""
p.write_text(s,encoding='utf8')
print('Current human docs now bind the actual 224-source mixed-boundary audit.')

