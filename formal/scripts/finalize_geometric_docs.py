from pathlib import Path
import json,shutil
root=Path(__file__).resolve().parents[2]
v=json.loads((root/"formal/audit/analysis-validation.json").read_text(encoding="utf8"))
a=json.loads((root/"formal/audit/region-contour-declarations-validation.json").read_text(encoding="utf8"))
assert v["build_exit"]==v["axiom_audit_exit"]==0 and v["public_theorems"]>1669
n=v["public_theorems"]; src=v["project_lean_files"]; total=src+8; named=a["declarations_count"]
summary=f"分析{src-1}模块／{n}条公开定理／{src}源；核心125条定理及1模型、8源未变，共{total}份正式源、{n+125}条辅助定理。本轮新增9模块{n-1669}条定理。统一构建及标准 --trust=0 公理审计退出0（{v['validated_at']}）；{named}个新命名声明另逐项审计通过，仅Classical.choice、Quot.sound、propext，无占位、自定义公理或内核绕过。新Lean源码无警告；仅既有batteries仓库本地修改提示。"
old="分析119模块／1669条公开定理／120源；核心125条定理及1模型、8源未变，共128份正式源、1794条辅助定理。本轮新增12模块224条定理。 2026-10-17T00:30:23.110663+08:00统一构建及标准 --trust=0审计退出0；286个新命名声明另逐项审计通过，仅Classical.choice、Quot.sound、propext，无占位、自定义公理或内核绕过。新Lean源码无警告；仅既有batteries仓库本地修改提示。"
files=['README.md','HANDOFF.md','STATUS.md','formal/LEAN_README.md','formal/FORMALIZATION_MAP.md','阶段性成果_2026-10-14.md','复盘与后续路线_2026-10-14.md','形式化独立核查_2026-10-14.md','deliverables/README.md']
snap=root/'archive/docs/2026-10-17-before-geometric'
snap.mkdir(parents=True,exist_ok=True)
for name in files:
    p=root/name
    backup=snap/name.replace('/','__')
    if not backup.exists(): shutil.copy2(p,backup)
    s=p.read_text(encoding='utf8').replace(old,summary)
    s=s.replace('PROGRESS_2026-10-17_CONTOUR_FOUNDATION.md','PROGRESS_2026-10-17_GEOMETRIC_CONTOUR.md').replace('audit/contour-foundation-semantic-review.md','audit/geometric-contour-semantic-review.md').replace('audit/contour-foundation-independent-evidence.json','audit/geometric-contour-independent-evidence.json')
    s=s.replace('05:05同聊天一次唤醒，id05-05已实际ACTIVE核实','05:05同聊天一次唤醒已处理并停用05-05').replace('05:05一次接续已安排','05:05一次接续已执行并停用').replace('今天05:05同聊天一次唤醒已核实','今天05:05一次唤醒已处理并停用，不再创建提醒')
    s=s.replace('仍缺占据区域frontier识别、连续简单曲线桥、一般Good保持／面积','已完成真实区域frontier识别、连续简单闭曲线、真正欧氏弧长和初态Good；仍缺一般Good保持／面积')
    s=s.replace('主缺口仍为实际方格并frontier与连续simple curve桥、Good保持和面积','主缺口为一般Good保持和面积')
    s=s.replace('本轮完成真实边界半边、截面、周长与包围盒、实际连通和无夹点、覆盖全部边界的单一离散循环，以及完整实参数边段仅可共端点的证明。','本轮完成实际方格区域frontier等式、完整边界的连续简单闭曲线、原单位方格搬运、真正欧氏弧长和最小矩形，并证明实际clip初态满足几何Good。')
    s=s.replace('frontier未开始证明的计划单独标注','真实frontier、连续曲线、欧氏全分割弧长及初态Good已验收；一般Good保持与核心尾未证')
    s=s.replace('当前交接：轮廓基础已验收，继续区域边界','当前交接：真实几何初态已验收，继续Good更新与面积')
    s=s.replace('真实轮廓基础已验收','真实几何轮廓与初态Good已验收')
    s=s.replace('286新命名声明在contour-foundation-declarations-validation.json',str(named)+'新命名声明在region-contour-declarations-validation.json')
    s=s.replace('128源、1669分析＋126核心公理输出和旧107proof modules未改',f'{total}源、{n}分析＋126核心公理输出和旧119proof modules未改')
    s=s.replace('frontier稿尚未开始，不在正式源中；两代理接续交接在formal/audit/region-frontier-handoff.md与region-boundary-handoff.md，formal/drafts/GridCellRegion.plan.md只是计划。','frontier两包含及完整连续/物理桥已实际构建验收，region交接记录现为完成状态。')
    s=s.replace('按 [NEXT_PHASE](formal/NEXT_PHASE.md) 构造放大闭cell有限并region，证明frontier恰等于全部真实暴露闭线段，再把已证全边界单cycle／无重复顶点／不交段接成连续simple closed curve。','按 [NEXT_PHASE](formal/NEXT_PHASE.md) 推进一般Good对应的行列凸性与真实更新分类，再证明保持和已删面积。')
    s=s.replace('离散单循环还不是原方格并frontier等式；','本轮已补原方格并frontier等式与连续单轮廓；')
    s=s.replace('无frontier识别、连续simple curve或Good保持','实际frontier和连续simple curve已由本轮新模块连接；一般Good保持仍缺')
    p.write_text(s,encoding='utf8')
nexttext=r"""# 下一阶段：真实Good更新、角点及首退出面积

2026-10-17。真实区域frontier、连续简单闭曲线、原单位cell搬运、真正欧氏弧长和实际clip初态Good已完成，见[本轮记录](PROGRESS_2026-10-17_GEOMETRIC_CONTOUR.md)。不重做旧模型、概率law、∞、原尺寸／exact-N和原过程比较。

下一步从实际四邻更新展开：

1. 对row/column convex的实际S，证明空位不可能同时有东西或南北两个占据邻点，故不能有三个占据邻点；对cleanup稳定S，所有占据点degree≥2。由此得到真实rawStep的非平凡翻转只能是degree2公平tie。此为局部分类，不能自动推出删除细颈仍连通。
2. 连接原GeometricGood的最小frontier周长与行列凸、四连通；或直接从实际初态建立更强离散不变量并证明沿真实modifiedStep保持。一般Good等价链尚未证明，不可当字段偷加角点、漂移或面积结论。
3. 利用真实innerDiamond包含、clippedDomain及边界规则排除夹点／细颈；证明山谷±1和实际cleanup顶点−2分类、Good保持与角点计数。
4. 首次失去D∪外四邻边界时，从真实轮廓推出相关外向区域确实被删，再调用已有四向格点块下界。单纯块card不是已删面积。

物理停止演化／实际生成元、CMST/FSS自含核心尾、严格二次尺度收缩和最终τ(N)=Θ(N²)仍未完成。事件索引不等于物理时间，端点law不等于停止过程law，不能把这些核心结论作最终参数。

有额度持续推进，不逐阶段停下汇报；05-05一次提醒已处理并停用，不建立周期或新提醒。沿用D:\MyWorks\Math与固定工具链；所有源变动须真实统一构建、标准Lean --trust=0逐声明审计、源指纹和独立AI语义核对。AI审阅不是人类专家认证。
"""
(root/'formal/NEXT_PHASE.md').write_text(nexttext,encoding='utf8')
(root/'formal/audit/geometric-contour-docs-counts.json').write_text(json.dumps({'summary':summary,'analysis_theorems':n,'analysis_sources':src,'formal_sources':total,'new_named':named},ensure_ascii=False,indent=2),encoding='utf8')
print(summary)
