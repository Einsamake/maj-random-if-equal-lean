from pathlib import Path
import json,shutil
root=Path(__file__).resolve().parents[2]
v=json.loads((root/'formal/audit/analysis-validation.json').read_text(encoding='utf8'))
a=json.loads((root/'formal/audit/update-stage-declarations-validation.json').read_text(encoding='utf8'))
assert v['build_exit']==v['axiom_audit_exit']==a['build_exit']==a['axiom_audit_exit']==0
assert v['public_theorems']>1798 and len(a['modules'])==8
n=v['public_theorems'];src=v['project_lean_files'];total=src+8;named=a['declarations_count']
summary=f"分析{src-1}模块／{n}条公开定理／{src}源；核心125条定理及1模型、8源未变，共{total}份正式源、{n+125}条辅助定理。本轮新增8模块{n-1798}条定理。统一构建与标准Lean --trust=0公理审计退出0（{v['validated_at']}）；全部{named}个新命名声明另逐项审计通过，仅Classical.choice、Quot.sound、propext。无占位、自定义公理或内核绕过，新源码无Lean警告，保留既有batteries本地修改提示。"
old=json.loads((root/'formal/audit/geometric-contour-docs-counts.json').read_text(encoding='utf8'))['summary']
files=['README.md','HANDOFF.md','STATUS.md','formal/LEAN_README.md','formal/FORMALIZATION_MAP.md','阶段性成果_2026-10-14.md','复盘与后续路线_2026-10-14.md','形式化独立核查_2026-10-14.md','deliverables/README.md']
snap=root/'archive/docs/2026-10-17-before-local-update'
snap.mkdir(parents=True,exist_ok=True)
for name in files:
 p=root/name;b=snap/name.replace('/','__')
 if not b.exists():shutil.copy2(p,b)
 s=p.read_text(encoding='utf8').replace(old,summary)
 s=s.replace('audit/geometric-contour-semantic-review.md','audit/update-stage-semantic-review.md').replace('audit/geometric-contour-independent-evidence.json','audit/update-stage-independent-evidence.json')
 s=s.replace('PROGRESS_2026-10-17_GEOMETRIC_CONTOUR.md','PROGRESS_2026-10-17_LOCAL_UPDATE.md')
 p.write_text(s,encoding='utf8')
rows='\n'.join('| '+m+' | '+str(v['theorems_by_module']['MathResearchAnalysis/'+m+'.lean'])+' |' for m in a['modules'])
content="""# 真实局部更新、清理与全轨迹周长预算：已统一验收

@SUMMARY@

| 新模块 | 公开定理数 |
|---|---:|
@ROWS@

行列凸且稳定的实际有限负自旋集合，其真实rawStep发生改变时只可能degree=2平局：空位tie=true出生，已占据点tie=false死亡。actual modifiedStep分类保留真实cleanup，没有把它替换成任意字段。上一轮8条standalone draft已纳入正式模块扩至16条，此处按完整统一记录计数。

出生一支已闭合：degree2空位必有一水平、一竖直占据邻点，插入保持行列整数区间凸、稳定和四邻连通，cleanup不再删除点；横纵实际坐标投影集合都不变。该结论不覆盖degree2死亡。

合法degree<2清理删除及任意合法链保持行列凸和四邻连通，进而真实cleanup也保持这些性质。删除侧另给精确条件：Stable S时erase v稳定恰为各占据邻点原degree≥3；conditional双删结果以所有存活点的明确原degree余量为前提，再由实际合法删除和终态唯一性识别cleanup。没有证明原Good几何自动提供该余量。

周长始终是真实暴露单位侧边数。任意有限S的插入满足P(insert v S)+2degree(S,v)=P(S)+4；删除满足P(erase v S)+4=P(S)+2degree(S,v)。真实多数raw/masked/modified Step与Word的P都非增，无Stable、凸性或Good前提。每个严格清理删除至少降低P两单位，沿真实状态递归的额外清理总删点数wordLoss满足 P(final)+2wordLoss≤P(initial)。这不把raw死亡算进额外清理。

对实际clip初态得到P(final)+2wordLoss≤8L+4、wordLoss≤4L+2。ClippedPerimeterBudget使用既有真实ClockEventWord.word及身份fair marks，clockOccupied的有限配置精确等于DropletClockLaw.endpoint true。预算点态适用于该真实改造过程每个物理端点，未将它冒充原raw过程的预算或停止链／生成元／二次恢复尾。

[统一证据](audit/analysis-validation.json)、[全部新增命名声明](audit/update-stage-declarations-validation.json)、[独立审阅](audit/update-stage-semantic-review.md)、[独立指纹证据](audit/update-stage-independent-evidence.json)、[反例和后续路线](audit/update-stage-route-review.md)。旧128 proof模块及8核心源不变。独立AI不冒充人类专家，条数不是完成率。

完整τ(N)=Θ(N²)主定理仍未完成。一般GeometricGood与离散凸/连通等价、实际大保护域排除死亡细颈、一般Good保持、角点漂移和首退出已删面积、物理停止演化／生成元、自含CMST/FSS核心尾与最终常数仍缺。相邻degree2死亡也可能断连通，L=1可出现一次总删3点，见独立反例；不能将出生或legal cleanup结论误用于raw degree2死亡。
""".replace('@SUMMARY@',summary).replace('@ROWS@',rows)
(root/'formal/PROGRESS_2026-10-17_LOCAL_UPDATE.md').write_text(content,encoding='utf8')
handoff="""# 当前交接：真实局部更新与周长预算已验收

@SUMMARY@

目标是原无限二维同步四邻、独立公平tie、有限扰动到H₂的最坏扩展期望τ(N)=Θ(N²)。**完整主定理未完成。** 保留∞、原尺寸/exact-N、真概率law、边界及时间尺度；禁止占位、自定义公理、内核绕过或核心结论最终参数。

本轮[八模块记录](formal/PROGRESS_2026-10-17_LOCAL_UPDATE.md)新增实际翻转分类、出生保凸/稳定/连通/投影、真实cleanup保凸和连通、精确条件单删/双删、任意状态多数更新与清理的周长Lyapunov及累计删点预算，并接到原有真实改造时钟端点。此前[原单位frontier/连续简单曲线/欧氏弧长/初态Good](formal/PROGRESS_2026-10-17_GEOMETRIC_CONTOUR.md)、实际模型/marks/law/∞/尺寸和比较全部保持。

下一步见[NEXT_PHASE](formal/NEXT_PHASE.md)。首先由实际innerD⊆S⊆clip、凸与稳定排除degree2对置细颈；已有正确数学路线但尚未Lean证明。再排除相邻删除造成夹点，处理真实cleanup双删局部余量；不能从本轮性质自动推出一般Good保持。原Good离散等价、首退出面积、生成元/停止law、CMST/FSS核心尾及最终二次常数仍缺。

本轮分析统一记录analysis-validation.json、全部新named update-stage-declarations-validation.json；[独立审阅](formal/audit/update-stage-semantic-review.md)及[独立证据](formal/audit/update-stage-independent-evidence.json)逐源核对。不按条数报完成率，不把AI当人类专家。先前1798基线在formal/audit/history/2026-10-17-0532/。

用户已授权有额度持续，不按阶段停下汇报。05-05一次提醒已处理并PAUSED，旧三个已删除，不新增提醒或周期轮询。实际工作区D:/MyWorks/Math，旧C路径不存在；D写入/构建已授权但当前沙箱需require_escalated，命令显式D workdir，同权限查重Lean。核心Lean4.35.0，分析4.35.0-rc4，mathlib54c01c3314d33d15d77893cbe4e0472ff26bb34d；复用缓存，不重下/重置/跨olean。

验收：formal/scripts/validate_analysis.py与audit_update_stage.py；文档和包scripts/validate_workspace.py、formal/scripts/package_lean.py。当前包deliverables/Lean形式化材料_2026-10-17.zip、LEAN_MANIFEST和audit/package-validation.json逐文件读回。检查点不写入自身包SHA，避免自引用。不购买额度/使用重置券/切API，不联系作者、发布或新建用户聊天。
""".replace('@SUMMARY@',summary)
(root/'HANDOFF.md').write_text(handoff,encoding='utf8')
(root/'STATUS.md').write_text('# 当前研究状态\n\n'+summary+'\n\n完整原主定理未完成。本轮关闭真实局部更新、出生保持、cleanup保凸/连通、周长单调及累计清理预算；一般Good保持、大保护域死亡几何、核心尾与最终二次界仍缺。用户授权额度内持续，旧提醒不恢复。\n\n[成果](formal/PROGRESS_2026-10-17_LOCAL_UPDATE.md)、[独立复核](formal/audit/update-stage-semantic-review.md)、[交接](HANDOFF.md)。\n',encoding='utf8')
(root/'formal/audit/update-stage-docs-counts.json').write_text(json.dumps({'summary':summary,'formal_sources':total,'analysis_theorems':n,'analysis_sources':src,'new_named':named},ensure_ascii=False,indent=2),encoding='utf8')
print(summary)
