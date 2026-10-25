"""Write reader-facing records only after actual complete finite-machine validation."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];F=R/'formal';A=F/'audit'
d=json.loads((A/'analysis-validation.json').read_text(encoding='utf8'))
assert d['build_exit']==d['axiom_audit_exit']==0
assert 'MathResearchAnalysis/MixedClockDynkin.lean' in d['source_sha256']
n=d['project_lean_files'];t=d['public_theorems'];total=n+8;outputs=t+126
summary=f"分析{n-1}个证明模块、{t}条辅助定理、{n}份分析源；核心旧125条定理及1模型、8源核对指纹未重编。合计{total}份正式源、{t+125}条辅助定理与1模型，{outputs}项实际公理输出。本次分析统一构建与标准Lean --trust=0审计实际退出0（{d['validated_at']}）；仅三个标准公理，完整源集及SHA绑定。"
phase='PROGRESS_2026-10-26_FINITE_MACHINE_DYNKIN.md'
modules=['MachineTraceTelescope','MachineEventScores','FiniteObservedClockState','ClockTimeNullGraph','FiniteMachinePreState','MachineClockDynkin','MachineClockGenerator','MixedClockDynkin']
rows=[]
for name in modules:
 key='MathResearchAnalysis/'+name+'.lean'
 assert key in d['source_sha256']
 rows.append(f"| {name} | {d['theorems_by_module'][key]} | `{d['source_sha256'][key]}` |")
progress=r"""# 从逐次变色，推进到真实时间中的平均变化公式

本阶段完成的是辅助混合边界过程的真实时间公式。此前只证明了“每次有效变色对应粒子和邻位交换”；现在还证明：让原来的随机时钟实际运行，任意观测量的平均变化，确实等于逐时刻平均变化速度的积分。这补上了有限计算与真实随机过程之间的一段连接。

时间仍是每个格子每单位时间平均响铃一次的物理时间；不是把整个方框所有响铃数当成时间。每次响铃只更新该格，两种硬币结果各占一半。若把时刻s的图形记为X_s，把某个数值特征记为F，证明的公式为

$$\mathbb E[F(X_T)]=F(X_0)+\int_0^T\mathbb E\left[\sum_v\left(\frac{F(U_{v,0}X_s)+F(U_{v,1}X_s)}{2}-F(X_s)\right)\right]ds.$$

这里U表示真的更新操作。每格的“减旧值”都在求和括号里面；不存在重新抽取状态分布、假设所需微分方程或更改时钟速率。

## 为什么这一步需要证明

判断一次变色时，必须使用响铃前的图形。我们从已经发生的事件和已揭示硬币重建图形，证明它确实只读取过去；再构造可预测的严格前态。在同一个满概率样本集合上，它对所有时刻——包括随机响铃时刻——都等于真实严格过去执行结果。

响铃前后图形可能不同。可数的响铃时刻对普通时间积分没有贡献，因此可在时间积分里改用当前图形；这个结论不能用来把随机响铃时刻的前态换成后态。新的可数事件时间图引理真正证明了零测度和交换积分顺序的依据。

之后建立真实有限事件望远镜求和、逐格逐标记重排与可积性，再调用此前已证明的原随机分布下有符号补偿。最后将任意有限状态机器实例化成真正的混合边界图形，并用已证阶梯/粒子算子等式识别粒子交换形式。

## 当前边界

原同步恰N尺寸二次期望下界已经完成。本阶段没有完成二次上界，也没有证明粒子负相关、随时间的矩微分方程、跨尺寸时钟分布对应或最终Theta结论。接下来把真实积分公式转成粒子平均位置和波动大小的方程，再证明平方时间内的清空概率。

索引仍沿原DropletClockLaw.Sample L，即clock参数2L−1，L≥1时实际边长2L+1；未声称本次把原概率基础推广到所有偶数边长。

## 实际核验

"""+summary+"\n\n新增模块与冻结指纹：\n\n| 模块 | 新定理数 | SHA256 |\n| --- | ---: | --- |\n"+'\n'.join(rows)+"\n\n[实际统一验收](audit/analysis-validation.json) · [标准内核实际输出](audit/analysis-axioms.log) · [前态与Dynkin专项声明审计](audit/finite-machine-dynkin-stage-declarations-validation.json) · [独立AI审查与边界](audit/finite-machine-independent-review.md)。\n\nAI复核不等于人类专家认证；本阶段未联系作者、对外公开或运行远端CI。\n"
(F/phase).write_text(progress,encoding='utf8')
p=R/'README.md';s=p.read_text(encoding='utf8')
old='接下来要证明真实时间里的平均运动满足相应方程，再估计恢复速度。二次上界仍未完成。'
new='现在也已证明真实时钟运行下的平均变化公式：平均变化等于逐时刻平均变化速度的积分。接下来要用它控制粒子平均位置和波动，证明平方时间内有足够大的清空概率，再接回原同步模型。二次上界仍未完成。'
assert old in s;s=s.replace(old,new)
s+='\n[26日：真实随机时间下的平均变化公式](formal/'+phase+')。\n';p.write_text(s,encoding='utf8')
status="""# 当前进度：二次下界已完成，上界的真实时间公式已接通

目标是τ(N)=Θ(N²)，即最坏平均恢复时间同时被两个固定常数乘N²夹住。完整主定理仍未证明。

## 已经完成

原同步模型的下界已经严格建立：存在尺寸恰为N的图形，平均至少需要cN²才能恢复。它涵盖无限方格、原独立硬币、边长奇偶和黑白背景互换；永不恢复的路径仍按无穷计算。

上界路线目前采用一个保留更多黑格的辅助混合边界过程。已证明它保持阶梯形状，且阶梯与一维粒子排列能互相还原；有效变色与相邻粒子/空位交换双向对应。

本次进一步接通真实时间：在原时钟和原硬币分布下，图形任意数值特征的平均变化等于其平均变化速度的时间积分。证明真正使用响铃前状态，并处理随机响铃时刻与普通时间积分的区别。

## 还缺什么

还要把真实积分公式转成粒子平均位置和波动的方程，证明粒子扩散足够快，再完成不同大小区域的时钟对应和原同步恢复上界。现有重启工具只有在清空成功概率界证明之后才能使用。

所以“时间公式已证明”不等于“恢复速度已估计出来”；二次上界与最终Theta仍未完成。

## 怎样核验

"""+summary+"\n\n新增声明有实际专项审计与独立语义/源指纹绑定。AI审查不等于人类专家认证。\n\n"+f"[本次结果与完整证据](formal/{phase}) · [源码与工具链](docs/VERIFICATION.md) · [3×3例子](README.md)\n"
(R/'STATUS.md').write_text(status,encoding='utf8')
for rel in ['formal/LEAN_README.md','formal/FORMALIZATION_MAP.md']:
 p=R/rel;s=p.read_text(encoding='utf8');s=re.sub(r'分析224个证明模块[^\n]+',summary,s,count=1)
 s+='\n[26日：有限机器的真实时钟Dynkin与混合边界实例]('+phase+')。\n';p.write_text(s,encoding='utf8')
verification='# 验证记录\n\n'+summary+"\n\n分析使用Lean4.35.0-rc4和固定mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d；核心使用Lean4.35.0，当前八源与原验收指纹一致，未在本阶段重编。所有新增使用原工具链与缓存。\n\n分析验证脚本实际统一build，再以标准Lean --trust=0逐定理审计；新增专项另外覆盖def/abbrev等命名声明。完整源集、SHA、实际输出名字及顺序另经绑定。只有Classical.choice、Quot.sound、propext；零新增Lean警告，仅既有batteries文档local-change提示。无sorry/admit、自定义公理、unsafe、native_decide或内核绕过。\n\n完整主定理尚未完成。原同步exact-N二次下界已完成；真实辅助时钟Dynkin已完成，矩方程、协方差、跨尺寸时钟与二次上界仍未完成。独立AI审查不等于人类专家认证；本地构建不等于远端CI。\n\n"+f"[本阶段公式、边界与逐源证据](../formal/{phase}) · [独立AI审查](../formal/audit/finite-machine-independent-review.md) · [统一验收JSON](../formal/audit/analysis-validation.json) · [读者进度](../STATUS.md)\n"
(R/'docs/VERIFICATION.md').write_text(verification,encoding='utf8')
ledger="""# 2026-10-26：可复用的方法记录

这是一份本项目的方法记录，不是外部新颖性认证。候选恢复上界仍未证明。

1. **让确定性有限机器与随机规律分开。** 把状态、初态和单步更新泛型化，保持原clock和身份标记分布不动；旧的清理冻结Dynkin不能直接套新规则。真正的通用桥应先重建过去状态，再由原补偿推导公式。
2. **用完整过去fiber解决全样本适应性。** 原总事件字的fallback依赖全局Good，可能读取未来；不能仅凭AE正常或ambient可测就说它适应。新的观察图只使用已经发生的身份和硬币，异常路径返回初态；在同一AE集合上所有实数时刻等于原过程。
3. **零测时间图比先证明整个current过程联合可测更短。** 对可数事件时间族，每条路径的响铃时刻可数；其图可测才允许换AE顺序。这样从可预测前态的有界可积性，通过真实时间AE相等运输到current，而不是误把随机ring本身也当成非响铃时刻。新引理已实际证明；它不要求事件时间独立或每个到达时间本身无原子。
4. **先建立真积分方程，再推微分方程。** 本阶段只完成实际Dynkin。候选下一步利用有界积分得到矩连续性，再用有限线性算子与微积分基本定理；这个后续简化尚未验收，不能写成已经证明的ODE。

这些方法解决的是工程和逻辑连接；没有据此认定原公开问题已解决或方法具有全球首次新颖性。
"""
(R/'research/followup/METHOD_LEDGER_2026-10-26.md').write_text(ledger,encoding='utf8')
(R/'deliverables/README.md').write_text(f"# Lean形式化材料\n\n最新材料包为Lean形式化材料_2026-10-26.zip，包含{total}份与实际验收匹配的正式源及证明、核验和交接材料。ZIP内逐文件长度、SHA和CRC均由打包脚本读回核验；准确总数及指纹见formal/audit/package-validation.json和同名.zip.sha256。\n\n原同步二次下界已完成；真实辅助过程时间公式已接通，二次上界和完整主定理仍未完成。\n",encoding='utf8')
print(json.dumps({'formal_sources':total,'analysis_theorems':t,'actual_axiom_outputs':outputs,'phase':phase},ensure_ascii=False))
