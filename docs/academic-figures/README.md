# 证明方法配图

四幅图分别表示零权层、正部平方能量、阶梯—粒子编码和保护失守的加权阈值。几何、颜色状态、权重与有限算例沿用原证明说明，图题和标注按当前学术文稿整理；原图与原验证记录保持不变。

[绘图程序](render_figures.py)使用 Pillow 绘制几何和曲线，以有理数核对有限漂移与支持不等式；指数时间或自动机轨迹均未在这些图中模拟。这些计算仅验证所列有限实例。每幅图的条件、算例及图像指纹由 [toy-checks.json](toy-checks.json)记录。任意状态结论由正文引用的 Lean 定理证明，不从有限检查外推。

在具有 Microsoft YaHei 或 Noto Sans CJK 字体的环境中，从仓库根目录运行 `python docs/academic-figures/render_figures.py`。字体与渲染器变化可能改变图片字节；数值条件应按数据文件复核。

[加权面积](../proof-discovery/02-boundary-weight.md) · [比较原理](../proof-discovery/03-positive-energy.md) · [局部清空](../proof-discovery/04-enough-probability.md)
