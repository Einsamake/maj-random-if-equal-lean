# 上界准备：真实混合边界与阶梯形状

原同步exact-N二次下界已完成，完整二次上界与Θ仍未完成。本阶段建立上界候选辅助过程的真实确定性与同维时钟基础，不证明其恢复概率。

## 严格完成的内容

MixedSquareModel在现有有限边长n+2上定义实际混合边界：西/南外部0、北/东外部1，交角由负坐标优先0。内部四邻不读对角交点。沿用原四输入majority、排中心和真实tie mark；原zero-boundary同尺寸单点更新在同mark下不超过mixed更新。

MixedSquareCorners证明空间Monotone（白色SW downset）的精确翻转分类：1变0恰须南/西0且tie=false；0变1恰须北/东1且tie=true。真实单点写入及任意有限identity-mark事件词保持形状；两个方向均保留，未将过程改为永久擦除。

MixedSquareClockLaw直接使用原ClockEventWord.word的逆序和原identity-indexed标记z.2，异常空字fallback相同。有限vector只用于可测重构，不重新抽样，也不宣称重复身份时独立fresh law。实际endpoint可测；原zero-boundary与mixed整词逐样本支配给真实同维nonzero概率比较；从全1起，所有样本、所有实数时刻的endpoint都保空间Monotone。这个形状结论不宣称旧globally-guarded word对原历史逐样本适应。

## 未完成的内容

这只比较相同有限区域，没有原N区域到更大M区域的clock限制law；没有完整SSEP编码、条件flip率生成元、一二矩ODE、Poincare或协方差概率界。mixed全0也会从NE边界重新生1，因此不能把它当吸收态或调用原恢复时间restart。

下一阶段推荐用实际每行白格数λ_y和p_r=r+λ_(r.rev)编码有限粒子。右半粒子数J应等于白色对角格数，核心接口f(d,d)=false iff d.val<J避免N−1截断减法。有关接口仍是下一阶段待证计划。

## 实际验收

分析215个证明模块、2878条辅助定理、216份分析源；核心125条定理及1模型、8源未变。合计224份正式源、3003条辅助定理与1个模型，完整公理输出3004项。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-25T19:15:50.773420+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，本次未重编核心。

本批3模块52条新定理、63项命名声明，三个专项分别32、18、13named均实际build0及标准trust0审计0，零新Leanwarning。旧221完整JSON/build/输出/入口和表存audit/history/before-mixed-square-stage-2026-10-25；下界4模块数学源未改。

[独立语义审查](audit/mixed-square-independent-review.md) · [224源完整绑定](audit/mixed-square-independent-final-binding-evidence.json) · [统一核验](audit/analysis-validation.json) · [真实时钟接口源码](analysis/MathResearchAnalysis/MixedSquareClockLaw.lean)。

独立AI不是人类专家认证。没有sorry/admit、自定义公理、native_decide、unsafe或内核绕过；没有把想证的核心上界当最终参数。
