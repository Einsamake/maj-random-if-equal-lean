# 形式化验证与复现

## 已归档的内核检查

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

本次修订仅改变说明文稿与其配图。源指纹检查和链接检查与重新运行 Lean 是不同操作，本次只核对文档与源指纹，未重新构建数学工程。旧验证 JSON 中的文稿指纹对应旧稿，详见[版本约定](ARCHIVAL_RECORD.md)。

内核检查约束的是具体形式声明及其依赖。原模型对应关系另有[独立 AI 语义复核](../formal/audit/original-theta-independent-review.md)；模拟本科读者反馈用于核查解释的可理解性。这两项均不属于独立人类专家评审。仓库不以这些检查代替文献优先权判断。

## 当前文稿的只读检查

在包含基线提交历史的 Git 检出中，可从仓库根目录运行：

```text
python scripts/check_documentation.py
```

该命令按[本次清单](academic-revision-2026-11-07/manifest.json)核对当前文稿、链接、267份正式源、54份研究 Lean 源文件及保留归档的字节一致性，并复算所列有限算例；它不调用 Lean。数学正文与资料入口见[文稿索引](INDEX.md)。
