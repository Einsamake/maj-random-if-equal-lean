# CMST保护域原文核对

来源：[Caputo–Martinelli–Simenhaus–Toninelli, arXiv:1007.3599v2](https://arxiv.org/html/1007.3599v2)，版本2010-09-14，本次直接读取2026-10-16。

- §3末 More notational conventions：离散集合边界是集合外、与集合内某点欧氏距离1的整数格点；在Z²上即外四邻边界。§2已用该边界设置模型。
- §8 Definition 7(e)：D的格点满足|x|+|y|≤(9/10)L；Lean使用完全等价的整数不等式10(|x|+|y|)≤9L，并保留原来的非严格≤。
- Definition 7后的改造动态：首次退出检查整个D∪∂D；只保护D会改变停止条件。
- 本模块实际证明D∪∂D恰为既有boundaryBand的全部格点；因此不是任意放大的替代保护域。也证明L≥1时它包含于实际剪角域，L≥40时接已有四向块及L²/1600基数下界。

本阶段只闭合保护域几何和真实初态包含。没有证明Good轮廓、退出时已删面积、停时law或二次概率界。
