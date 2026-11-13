# Qatlib 开发与验证脚本

> 🌐 [English version](./README.en.md)

本目录包含在 [`lakefile.toml`](../lakefile.toml) 中注册的 Lean 维护与内核审计可执行工具，以及文档门户构建脚本：

- **`get_cache.lean`**（`lake exe get_cache`）：
  按 [`lake-cache.toml`](../lake-cache.toml) 自动拉取上游 `Mathlib`、`Physlib` 与 `Qatlib` 三层预编译构建缓存。
- **`lint.lean`**（`lake lint` 或 `lake exe lint`，在 `lakefile.toml` 中配置为 `lintDriver = "lint"`）：
  只读静态源码、风格与导入图检查器（全库耗时约 1 秒）：
  1. **源码与风格检查**：校验标准 Apache-2.0 版权头、`Qatlib/` 允许的顶层目录（`Foundations`、`Concepts`、`Papers`）、严格的 `UpperCamelCase` 目录与文件名、全仓大小写不敏感路径零碰撞（`ERR_CASE`）、Unix `\n` 换行符、无行尾多余空白、分号前无空格，以及不含调试型 `set_option` 指令。
  2. **模块树与单向分层检查**：校验 `Qatlib.lean` 按字典序完整导入 `Qatlib/` 下所有模块、库内无裸 `import Mathlib`、所有 `import Qatlib.*` 均指向真实源码文件，并静态强制单向分层依赖 `Foundations ← Concepts ← Papers`（反向依赖报告 `ERR_LAY`）。
- **`test.lean`**（`lake test` 或 `lake exe test`，在 `lakefile.toml` 中配置为 `testDriver = "test"`）：
  Lean 4 内核级 `.olean` 环境健全性与公理审计器。将编译后的 `Qatlib` 环境加载至 Lean 4 内核，并通过 `Lean.collectAxioms`（传递公理闭包）逐条验证全库所有声明均为零 `sorry`（`0 sorryAx`）、未使用未经内核验证的计算规约（`Lean.ofReduceBool` / `native_decide`），且仅依赖 Lean 的三条标准公理（`propext`、`Classical.choice`、`Quot.sound`）。
- **`build_site.py`**（`python3 scripts/build_site.py`）：
  纯 Python 静态文档门户生成脚本，将中英文指南、全库模块导览、文献索引（`docs/references.bib`）与 `doc-gen4` API 参考文档组装为统一的 GitHub Pages 站点（工作流见 [`.github/workflows/docs.yml`](../.github/workflows/docs.yml)）。
