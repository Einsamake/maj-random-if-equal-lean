# 形式化验证与复现

## 当前修订的验证入口

2026-11-17 A/B 修订的[验收记录](../research/revision-ab-2026-11-17/validation.json)涵盖原 267 份项目源的重新编译，以及 5 个新模块的 58 个命名声明和 2 份强化下界依赖的 47 项声明。统一检查使用标准 Lean `--trust=0`；公理输出属于 `propext`、`Classical.choice`、`Quot.sound` 及其子集。外部锁定的 Lean/mathlib 依赖沿用已安装版本。

11 月 17 日版本的上下界、块尾和矩结论的原模型入口为 [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean)，方形极值为 [OriginalRecoveryResults.lean](../research/revision-ab-2026-11-17/lean/OriginalRecoveryResults.lean)。[统一构建记录](../research/revision-ab-2026-11-17/evidence/unified-build.json)、[原工程重建记录](../research/revision-ab-2026-11-17/evidence/base-replay/replay.json)和[独立最终绑定](../research/revision-ab-2026-11-17/evidence/independent-final-binding.json)保存实际命令、输出和文件指纹。记录中的本机绝对路径属于历史运行环境，复现时须按安装布局调整。

以下按版本列出构建与审计入口。

## 11 月 19 日下界补充

[复现脚本](../research/lower-bounds-2026-11-19/replay.py) 使用锁定的 Lean 4.35.0-rc4。先按本页说明构建 `formal/analysis`，再在仓库根目录运行 `python research/lower-bounds-2026-11-19/replay.py`，并用 `--lean` 指向该版本的编译器。脚本重编四个前置模块、十五个本次审计的数学模块及审计入口，复用已构建的分析库与 mathlib。[逐项公理输出](../research/lower-bounds-2026-11-19/evidence/LowerAudit.log) 共 377 项，详见[验证记录](../research/lower-bounds-2026-11-19/evidence/validation.json)。

## 原封存版本的内核检查

主定理声明为 `MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic`。2026-10-26的[分析验证记录](../formal/audit/analysis-validation.json)记载：259份分析源统一构建成功，`lake env lean --trust=0 AnalysisAxioms.lean` 退出码为0，检查的3280条分析定理所输出的公理依赖属于 `propext`、`Classical.choice` 和 `Quot.sound`。

另8份核心源使用独立工具链；最终阶段核对了其源指纹与既有[核心审计](../formal/audit/core-validation.json)，没有重新编译这8份源。最终[独立绑定记录](../formal/audit/original-theta-independent-final-binding-evidence.json)汇总267份正式源及3406项公理输出。因而不能将最终阶段描述为两套工具链均重新构建。

| 工程 | Lean版本 | 依赖 |
| --- | --- | --- |
| `formal/analysis/` | `4.35.0-rc4` | mathlib提交 `54c01c3314d33d15d77893cbe4e0472ff26bb34d` |
| `formal/` | `4.35.0` | 以本目录的 `lakefile` 与锁定文件为准 |

固定版本分别记在[分析工具链](../formal/analysis/lean-toolchain)和[核心工具链](../formal/lean-toolchain)。不同 Lean 版本的编译产物不可混用。

## 在独立检出中复现

安装对应版本的 Lean/Lake 并恢复锁定依赖后，从分析目录运行：

```text
cd formal/analysis
lake build
lake env lean --trust=0 AnalysisAxioms.lean
```

核心工程在其独立目录及指定版本下检查（以下同样从仓库根目录开始）：

```text
cd formal
lake build
lake env lean --trust=0 audit/CoreAxioms.lean
```

本仓库不随附编译器和依赖缓存。首次构建需要取得工程锁定的依赖，并验证其版本与源一致。

`formal/scripts/validate_analysis.py` 与 `validate_core.py` 是原 Windows 工作区使用的验证脚本，编译器路径相对固定在 `formal/.tools/`。在使用其他安装布局时，宜运行上述 Lake 命令或明确调整本地脚本路径。原脚本会写入审计输出，复现应在独立检出中进行，以保留归档记录。

## 文档与历史证据

各轮文档修订与数学构建分别记录。旧验证 JSON 中的文稿指纹对应当时版本；当前文稿按新的清单检查，历史记录保持不变，详见[版本约定](ARCHIVAL_RECORD.md)。

内核检查约束的是具体形式声明及其依赖。原模型对应关系另有[独立 AI 语义复核](../formal/audit/original-theta-independent-review.md)；原版本的模拟本科读者反馈用于核查当时文稿的可理解性；本轮说明另由模拟的概率论与随机过程研究者阅读复核，反馈及指纹见[本轮记录](mathematical-introduction-2026-11-17/README.md)。这些 AI 复核与人类专家评审分别记录，文献出处见[参考文献](REFERENCES.md)。

## 当前文稿的只读检查

在包含基线提交历史的 Git 检出中，可从仓库根目录运行：

```text
python scripts/check_documentation.py
```

该命令按[当前清单](mathematical-introduction-2026-11-17/documentation-manifest.json)核对现行文档、链接、267 份正式源、54 份研究 Lean 源及原归档字节，并复算所列有限算例；它不调用 Lean。本轮另核对 A/B 已验收快照的全部 372 个文件，检查结果与独立模拟数学读者反馈见[本轮记录](mathematical-introduction-2026-11-17/README.md)。[上一版发布清单](ab-publication-2026-11-17/documentation-manifest.json)及更早清单作为历史版本保留。数学正文与资料入口见[文稿索引](INDEX.md)。

## 2026-11-17 A/B修订审计

[本轮验收](../research/revision-ab-2026-11-17/validation.json)记录267份项目源重新编译，以及5个新模块58项声明与2份强化依赖47项的标准Lean `--trust=0`统一审计。原267份源未修改，外部锁定依赖沿用现有安装。正文与实际输出另有独立AI语义和指纹核对；用户取消了本轮模拟读者验收。公开目录保存已验收字节及原命令记录，机器上的绝对路径是历史运行记录，合作者复现时须按本机布局调整。发布检查只核对已验收文件与仓库，不将其称为再次运行Lean。
