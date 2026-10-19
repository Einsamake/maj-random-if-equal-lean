# CMST具体保护集合阶段

2026-10-16。**完整原问题τ(N)=Θ(N²)未形式化。** 用户要求删除的三个旧提醒已由应用工具删除，旧状态目录已移除；当前仅使用 [证明检查点](../README.md)。

## 实际新证明

| 模块 | 公开定理 | 数学内容 |
|---|---:|---|
| ClippedProtectedGeometry | 23 | 有限内菱形D、原实数0.9L与整数定义等价、真实域外四邻边界、D∪∂D恰等于boundaryBand；L≥1包含clipped域，L≥40接四向点数和初态包含 |
| ProtectedDomainClockComparison | 11 | 保护顶点有限表示及recenter像精确相等、非空、clip内和初态全true；具体初态原过程概率实例；含∞首缺失事件索引正性与raw恢复比较 |

已直接重新核对[CMST v2](https://arxiv.org/html/1007.3599v2)的§3末边界约定、§8 Definition7(e)及其后停止规则。D满足10(|x|+|y|)≤9L，∂D是域外且四邻接D的点；保护集合确为D∪∂D。非严格不等式、整数取整及外边界均保留。

## 实际概率比较

L≥40时，任意物理t，原全负方形clock端点在t已全正的概率，不大于剪角改造端点的负自旋集合未包含D∪∂D的概率。两侧仍是实际rate1每格时钟和同一公平标记measure；较大端点逐样本等于旧ClockExecutionLaw.endpoint。有限保护spin全true已证明恰等价于真实集合包含D∪∂D；上一阶段任意I的非空与初始包含参数已由实际几何解除。

另定义concrete protectedExitIndex : ℕ∞，证明>0且≤同事件序列raw恢复索引。它仍是事件索引，不是物理首退出。初态包含在实际初始配置上证明，未把异常时钟样本t=0端点当成初态。固定t比较只涉及未冻结端点失败事件，不宣称停止后全路径支配。

四向块仍只提供集合包含、精确card和L²/1600下界；未证首退出时这些点已删。2-core仍不等于Good。

## 验收

分析107模块／1445条公开定理／108源；核心125条定理及1个模型定义、8源未变，共116份正式源、1570条辅助定理。本轮新增2模块34条定理。 2026-10-16T23:29:16.684465+08:00统一构建及标准 --trust=0审计退出0，42个新命名声明另逐项审计通过。仅Classical.choice、Quot.sound、propext，无占位、自定义公理或内核绕过；新Lean源码无警告，保留既有batteries本地改动提示。

新42个公开定义／缩写／定理均另逐项trust0；私有向内一步辅助经实际内核及公理依赖检查。旧105分析proof源和8核心源未改，新2源及总入口变化。核心沿用2026-10-14成功审计。

- [统一记录](audit/analysis-validation.json)、[新声明审计](audit/protected-domain-declarations-validation.json)。
- [独立AI报告](audit/protected-domain-semantic-review.md)、[116源及1571全局公理输出证据](audit/protected-domain-independent-evidence.json)。内部AI不是人类专家认证。
- [原文核对](audit/clipped-protected-geometry-source-note.md)、[旧提醒删除结果](../README.md)。

## 精确剩余

Good简单轮廓及更新不变性、首退出前已删面积、物理首退出及停止过程演化／生成元、自含FSS上尾和CMST下尾、二次尺度严格收缩及最终二次扩展期望仍缺。下一步从Good的真实离散边界编码、与原条件等价和clipped初态Good开始，见 [NEXT_PHASE](../README.md)。具体保护集合已闭合，不重做；定理条数不是完成率。
