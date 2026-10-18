# 复现与信任边界

先使用elan准备各目录lean-toolchain声明的版本。核心与分析必须分别构建，不复用跨版本olean。

核心：

```sh
cd formal
lake build
lake env lean --trust=0 audit/CoreAxioms.lean
```

分析：

```sh
cd formal/analysis
lake update
lake exe cache get
lake build
lake env lean --trust=0 AnalysisAxioms.lean
```

mathlib必须与lakefile.toml和analysis-validation.json中的固定commit一致；更新后若发生依赖漂移，应恢复清单并查明原因，不把不同依赖的结果视为原验收。仓库提供原本机成功日志与源指纹，没有声称全新远程CI已经运行。

analysis-validation.json绑定143分析源；core-validation.json绑定8核心源。新保护演化52命名声明和退出面积13命名声明另有专项日志与独立AI指纹复核。#print axioms检查覆盖1953分析定理和126核心声明，仅允许标准三公理。真正完整主定理目前不在已证声明中。

部分本机元数据路径已在导出副本中替换为<workspace>，正式Lean源码保持逐字节一致。SNAPSHOT_MANIFEST.json记录仓库快照各文件的SHA256；与工作区构建记录共同使用。
