[English](README.md) | [简体中文](README_zh.md)

# catalan-lean4

本仓库给出了卡塔兰猜想（Mihăilescu 定理）的 Lean 4 形式化证明。

相邻且均为非平凡完全幂的正整数只有 **8 和 9** 这一对。本仓库证明了这一结论，并对相应幂方程的解进行分类，涵盖非零整数底数为正或负的情形。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** Preda Mihăilescu 对卡塔兰猜想的证明。
- 借助 AI 辅助开发（Codex 和 Claude Code）；所有证明均经 Lean 4 内核验证。

## 主要结果

| 定理 | 陈述 |
| --- | --- |
| `Catalan.JSP.statement` | 8 和 9 都是非平凡完全幂；若正整数 `n` 与 `n + 1` 都是非平凡完全幂，则 `n = 8`。 |
| `Catalan.catalans_conjecture` | 对自然数 `a, b > 1` 和正自然数 `x, y`，若 `x^a - y^b = 1`，则 `a = 2`、`b = 3`、`x = 3`、`y = 2`。这里的减法采用自然数上的截断减法。 |
| `Catalan.catalan_int` | 对自然数指数 `a, b > 1` 和整数底数 `x, y > 1`，方程 `x^a = y^b + 1` 的解同样满足 `a = 2`、`b = 3`、`x = 3`、`y = 2`。 |
| `Catalan.catalan_int_signed` | 对非零整数 `x, y` 和自然数 `p, q ≥ 2`，若 `x^p - y^q = 1`（整数减法），则 `p = 2`、`q = 3`、`x = 3 ∨ x = -3`、`y = 2`。 |
| `Catalan.mihailescu_odd_primes` | 方程 `x^p = y^q + 1` 不存在底数为非零整数且两个指数均为奇素数的解。 |

这些定理的陈述与证明见 [JSP.lean](Catalan/JSP.lean)、[Final/Assembly.lean](Catalan/Final/Assembly.lean) 和 [Final/Signed.lean](Catalan/Final/Signed.lean)。可通过 `import Catalan` 导入这些结果。`Catalan.JSP.IsProperPerfectPower` 明确定义了非平凡完全幂：自然数底数和指数都至少为 2。

Google DeepMind 的 Formal Conjectures 仓库给出了陈述相同的 `Catalan.catalans_conjecture`，并把本仓库的证明链接为它的形式化证明（[Catalan.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Catalan.lean)，[PR #6452](https://github.com/google-deepmind/formal-conjectures/pull/6452)）。

## 构建与验证

环境要求：Git、Python 3.9 或更高版本，以及 [elan](https://github.com/leanprover/elan)，并确保 `lake` 已加入 `PATH`。请在仓库根目录运行：

```sh
lake exe cache get
./scripts/verify.sh
```

第一条命令会获取固定版本的 Mathlib 依赖及其编译产物缓存。验证脚本会校验随仓库附带的第三方源码，构建 `Catalan.Audit` 及其直接、间接导入的全部模块，检查公开定理陈述，并解析所有预期的公理报告。显式构建审计模块还会构建其额外导入的类域论模块。所有证明编译均使用 `--trust=0`。

若需在全新的 Lean 内核环境中，对五个公开定理所依赖的全部常量（依赖锥）进行重放检查，请运行：

```sh
./scripts/replay.sh
```

有关命令、输出位置，以及依赖的编译缓存、源码构建和内核重放之间的区别，见[验证详情](docs/verification.md)。最终定理仅使用 `propext`、`Classical.choice` 和 `Quot.sound`；不依赖额外公理或未证明的前提。

源码指纹和验证输出见[验证快照](Verification/RESULTS.md)。同一已提交证明版本的后续检查，包括全新 Linux 环境验证和 Mathlib 库的全量源码重建，见[补充验证证据](Verification/Supplemental/README.md)。

## 固定依赖

- Lean `4.33.1`，由 [lean-toolchain](lean-toolchain) 选定。
- Mathlib `v4.33.1`，提交为 `0df444a360eaa60ab8c11dca51a86af692955474`，由 [lake-manifest.json](lake-manifest.json) 固定。
- ClassFieldTheory 中的 871 个未修改模块，提交为 `2930b56f4b5c33ddab9ef91a45a4811d6f7a683f`，收录于 [vendor/ClassFieldTheory](vendor/ClassFieldTheory/README.md)。其路径和哈希值记录在 `SOURCES.json` 中。

[lakefile.toml](lakefile.toml) 为固定版本的 ClassFieldTheory 库设置了有限的 heartbeat 资源预算。项目不会自动更新这些源文件。

## 数学参考文献

- Preda Mihăilescu, [Primary cyclotomic units and a proof of Catalan's conjecture](https://doi.org/10.1515/crll.2004.048), *Journal für die reine und angewandte Mathematik* 572 (2004), 167–195.
- Yuri F. Bilu, [Catalan without logarithmic forms (after Bugeaud, Hanrot and Mihăilescu)](https://doi.org/10.5802/jtnb.478), *Journal de théorie des nombres de Bordeaux* 17 (2005), 69–85.

关于公开入口及其与 JSP-000035 的关系，见[定理陈述与证明指南](docs/mathematics.md)。

## 许可证

Apache-2.0；见 [LICENSE](LICENSE)、[NOTICE](NOTICE) 和[第三方来源与署名说明](THIRD_PARTY.md)。
