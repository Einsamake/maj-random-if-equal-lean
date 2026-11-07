# 图像、数据与复现

图分为有限算例、确定性编码示意和理论界的图示。它们与 Lean 定理的关系由以下来源说明确定，不能将有限轨迹或示意图解释为恢复时间的统计估计。

| 文件 | 内容与数据 |
| --- | --- |
| `01-rule.png` | 四邻同步投票；中心格不参与计数 |
| `02-evolution.png`、`03-evolution.gif` | 相同初态、随机种子0的一条同步轨迹；静态帧为0、1、2、7步 |
| `04-recovery-times.png` | 同一3×3初态在种子0、5、8下的恢复时间7、4、10；三个样本不代表理论期望 |
| `05-worst-case.png` | 最坏期望的定义示意；A、B、C不是模拟测量值，也不枚举全部初态 |
| `06-current-bridge.png` | 同步与单点更新的局部示意，不断言两过程的恢复时间相等 |
| `07-fresh-coin.png` | 固定点单标记的翻转配对，不单独证明多点未来独立性 |
| `08-local-change.png` | 普通更新的局部计算，不包含辅助过程的全部清理和漂移 |
| `09-clock-time.png` | 指定间隔0.6、1.1、0.9在截止2.2的占用分割：0.6、1.1、0.5，非随机模拟 |
| `06-particle-encoding.png` | 5×5混合边界下的合法角翻转与粒子邻位交换，未指定等待时间 |
| `07-local-clearing.png` | 原尺寸16、辅助边长129的局部清空构造；概率及期望常数来自理论界 |

图像由 [render_explainer.py](../render_explainer.py)、[render_clock_timeline.py](../render_clock_timeline.py)、[render_particle_encoding.py](../render_particle_encoding.py)和[render_mixed_clearing.py](../render_mixed_clearing.py)直接绘制。数据与指纹分别记录于[同步数据](simulation-data.json)、[时钟数据](clock-time-data.json)、[编码数据](particle-encoding-data.json)和[清空数据](local-clearing-data.json)。

同步模拟每次先读取完整旧状态，再统一写入新状态，并与逐格参考计算核对。显示窗口外不能出生的论证使用初始包围方框：框外一点至多有一个框内四邻，因此不足以产生黑格。图形有限窗口不替代无限模型定义。

安装 Python、NumPy、Pillow及可用的中文字体后，可在独立检出中运行绘图脚本。重绘可能随字体栅格化而改变图像字节；原指纹与所用环境按[版本约定](../ARCHIVAL_RECORD.md)解释。
