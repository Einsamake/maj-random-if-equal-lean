# 原作者与原文路线：公开先例检索

检索日：2026-10-26。独立检索代理：novelty_authors。这里只记录公开文献证据，不证明全球文献不存在，也不认证人类同行评议或优先权。

## 本轮结论

已直接核对原论文、作者更新到2026年的页面、2025综述与2026预印本。此路线没有发现同一无限二维同步四邻公平平局模型的二次恢复时间公开证明。原文的二次结论确实是猜想；2025综述仍只叙述三次上界。这个组合支持“尚未发现同模型公开先例”的有限判断，不能推出“截至今天绝对无人证明过”。

## 可复核来源

1. Fatès、Marcovici、Taati，*Self-stabilisation of cellular automata on tilings*。
   - arXiv: https://arxiv.org/abs/2101.12682
   - 实际读到的版本史：v1 2021-01-29；v2 2021-11-11；最新v3 2022-03-05。
   - 作者期刊PDF：https://marcovici.perso.math.cnrs.fr/Publications/Fates_Marcovici_Taati_FI2022.pdf
   - Fundamenta Informaticae 185(1):27–82 (2022)，DOI https://doi.org/10.3233/FI-222103
   - §1.2期刊p31定义扰动直径为最小平移半开正方形边长；§4.1期刊p54取恰该尺寸的确定初态之最坏期望。§4.2式(36)是不含中心的四邻同步规则，平局独立公平。Proposition4.1只给三次上界；p79 Question7.4提出二次猜想。目标是两个齐次背景。
   - Example4.2明确区分异步独立Poisson时钟模型。其引用Fontes–Schonmann–Sidoravicius的连续时间二次量级不能直接当作同步问题已解。

2. Irène Marcovici，*Cellular automata and self-organisation phenomena*。
   - 作者PDF：https://marcovici.perso.math.cnrs.fr/Publications/Marcovici_ESAIM2025.pdf
   - ESAIM Proceedings and Surveys80:17–25 (2025)，DOI https://doi.org/10.1051/proc/202580017
   - 已直接读全文。§3.2期刊p24描述四邻公平平局的各向同性同步规则，并叙述向有限tiling space扩展后的三次上界；没有给本题二次证明。
   - 文中“quadratic”在§2.1是另一种一维有限环的同步问题，不能与本题等同。本综述不是严格声明Q7.4在2025仍未解；只能说它没有报告二次改进。
   - 出版商PDF403，改用上述作者PDF成功，不把受限页面当已读。

3. Siamak Taati作者主页。
   - https://siamak.isoperimetric.info/
   - 实际读取页面末尾注明Last Update: September2026，列有2026/2025预印本与出版物。
   - 清单未见本题新解决条目；作者列表不一定穷尽，所以不能从缺席推断全球开放。
   - 主页链接的2024 CIRM报告 *Stabilising shifts of finite type with cellular automata*，https://siamak.isoperimetric.info/talks/Marseille-CSDS-2024.pdf ，已读86页文字。内容主要为确定CA与其他SFT复杂度，没有讨论本题Q7.4；因此不拿其开放问题列表作本题仍开放证据。

4. Irène Marcovici与Siamak Taati，*Positive-rate PCA and IPS with stationary Bernoulli measures are rapidly forgetful*。
   - https://arxiv.org/abs/2605.16904 ，v1提交2026-05-16。
   - https://arxiv.org/html/2605.16904v1 ，实际HTML标题注释Last update August24,2026。
   - 已读摘要与正文设置：要求严格正转移率及平稳Bernoulli测度，得遗忘/混合结果。原Maj-Random-If-Equal有吸收齐次态，不满足此正率假设；本论文不是本题有限扰动恢复时间的二次证明。

5. Irène Marcovici作者出版物列表。
   - https://marcovici.perso.math.cnrs.fr/
   - 本轮搜索索引实际显示2026与2025条目，定位了上面2025综述和2026预印本。多次直接open主页超时；因此未把整个主页说成直接逐项读完。

6. Nazim Fatès的HAL作者清单。
   - https://cv.hal.science/nazim-fates
   - 搜索索引返回2026/2025等条目及2023HDR *Robustesse des systèmes complexes : étude du rôle de l’aléa dans la dynamique des automates cellulaires*，HAL tel-04165486。
   - 多次直接open超时；HDR document端点被Anubis拒绝。未读完整HDR，不声称已排除其中藏有本题新界。

## 本轮检索词与限制

检索包括题名、arXiv编号、Question7.4、Maj-Random-If-Equal及空格/年份2023–2026组合、三作者与quadratic/recovery等。精确词与年份组合有时返回无关降级结果，已排除，没有把这些结果当命中或“零结果”证明。

这一路线覆盖原论文版本、作者清单、一个2025作者综述、2026作者预印本及2024报告。它没有完整覆盖所有引用该文的论文、所有学位论文、未公开手稿、私人通信或全网代码。后者必须由主检索路线与专家核对补充。没有联系作者、没有公开项目，也没有修改任何Lean证明或最终公理审计。

适合引用的措辞：截至2026-10-26，本轮已核公开作者材料中未发现同模型二次恢复时间定理的先例；原2022论文明确提出二次猜想，2025综述仍叙述三次上界。全球首创性尚不能据此认证。
