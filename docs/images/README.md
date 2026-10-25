# 这些图怎样得到

前八张图由 [render_explainer.py](../render_explainer.py) 用 Pillow 直接绘制，演化数据由 NumPy 生成；第九张由 [render_clock_timeline.py](../render_clock_timeline.py) 用 Pillow 绘制。没有用图像生成模型补画任何演化帧。

- `01-rule.png`：四邻投票示意，中心格旧颜色不投票。
- `02-evolution.png`、`03-evolution.gif`：种子0的一条真实同步轨迹。静态图抽取第0、1、2、7步，动图显示全部整数时刻。
- `04-recovery-times.png`：相同3×3初态，种子0、5、8的恢复时间分别为7、4、10。三次样本平均不是理论期望。
- `05-worst-case.png`：最坏平均恢复时间的定义示意。A、B、C是未知理论平均的标签，不是模拟测量值；图中三种不是全部初态。
- `06-current-bridge.png`：同步与单点更新的合法示意。左边四个平局角都选白，右边只更新一次左上角；不是两过程恢复时间相同的断言。
- `07-fresh-coin.png`：固定格点、有限合法观察时刻之后的单标记翻转配对示意，不是多格点未来独立性的证明。
- `08-local-change.png`：普通单点更新规则的局部算例，不冒充改造辅助过程的完整面积生成元或物理时间公式。

- `09-clock-time.png`：单格点时钟的时间轴分割示意。人为选定间隔0.6、1.1、0.9，截止2.2时有两次到达，三个占用长度0.6、1.1、0.5。用有理数精确核对总和为2.2；不是随机模拟或期望估计。数据、图像SHA及文字边界检查在[clock-time-data.json](clock-time-data.json)。

## 复现

安装 Python、NumPy、Pillow，并提供支持中文的字体后运行：

```text
python docs/render_explainer.py
python docs/render_clock_timeline.py
```

脚本优先使用 Windows 微软雅黑；Linux 可使用 Noto Sans CJK。环境版本、随机种子、所有硬币场、全部演化状态及图片SHA256在 [simulation-data.json](simulation-data.json)。

每次更新都先读取完整旧状态，再一次性得到新状态。脚本逐帧与独立的逐格参考计算核对；穷举四邻投票、两种中心旧颜色和两种平局标记共64种局部情形；核对首次全白时间和白色外框始终未变黑。

对于这个初态，黑格始终留在原3×3包围方框内；外侧点最多有一个来自方框内的邻居，因而不会变黑。7×7显示窗口不会把本来存在的黑色演化裁掉。

这些图是教学演示，既没有估计真实τ(N)，也没有证明二次尺度定理。形式化源码和既有Lean验收没有因绘图而改动。

## 粒子编码图

06-particle-encoding.png由[绘图源码](../render_particle_encoding.py)生成，数据见[JSON](particle-encoding-data.json)。5×5混合边界，白色行长从全0变为(1,0,0,0,0)，再变为(2,1,0,0,0)；粒子位置和三个合法相邻跳见数据。仅为合法更新顺序示意，没有随机等待时间，不是平均速度或概率证明。
