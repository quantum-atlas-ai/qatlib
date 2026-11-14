# Qatlib 开发与验证脚本

> 🌐 [English version](./README.en.md)

本目录包含在 [`lakefile.toml`](../lakefile.toml) 中注册的 Lean 维护与内核审计可执行工具，以及文档门户构建脚本：

- **`get_cache.lean`**（`lake exe get_cache`）：
  按 [`lake-cache.toml`](../lake-cache.toml) 自动拉取上游 `Mathlib`、`Physlib` 与 `Qatlib` 三层预编译构建缓存。
- **`lint.lean`**（`lake lint` 或 `lake exe lint`，在 `lakefile.toml` 中配置为 `lintDriver = "lint"`）：
  只读静态源码、风格、导入、语义忠实度与文献引用检查器：
  1. **源码与风格检查**：校验标准 Apache-2.0 版权头、`Qatlib/` 允许的顶层目录（`Foundations`、`Concepts`、`Papers`）、严格的 `UpperCamelCase` 目录与文件名、全仓大小写不敏感路径零碰撞（`ERR_CASE`）、Unix `\n` 换行符、无行尾多余空白、分号前无空格，以及不含调试型 `set_option` 指令。
  2. **模块树与单向分层检查**：校验 `Qatlib.lean` 按字典序完整导入 `Qatlib/` 下所有模块、库内不使用顶层全量入口 `import Mathlib`（按需导入具体 `Mathlib.*` 子模块完全允许）、所有 `import Qatlib.*` 均指向真实源码文件，并静态强制单向分层依赖 `Foundations ← Concepts ← Papers`（反向依赖报告 `ERR_LAY`）。
- **`test.lean`**（`lake test` 或 `lake exe test`，在 `lakefile.toml` 中配置为 `testDriver = "test"`）：
  Lean 4 内核级 `.olean` 环境健全性与公理审计器。将编译后的 `Qatlib` 环境加载至 Lean 4 内核，并通过 `Lean.collectAxioms`（传递公理闭包）逐条验证全库所有声明均为零 `sorry`（`0 sorryAx`）、未使用未经内核验证的计算规约（`Lean.ofReduceBool` / `native_decide`），且仅依赖 Lean 的三条标准公理（`propext`、`Classical.choice`、`Quot.sound`）。
- **`build_site.py`**（`python3 scripts/build_site.py`）：
  纯 Python 静态文档门户生成脚本，将中英文指南、全库模块导览、文献索引（`docs/references.bib`）与 `doc-gen4` API 参考文档组装为统一的 GitHub Pages 站点（工作流见 [`.github/workflows/docs.yml`](../.github/workflows/docs.yml)）。
- **`docs_cache.py` / `build_docs.sh`**：
  自维护的文档快照协议，使用 R2 存储，独立于 Lake 编译缓存；不是 `doc-gen4` 的稳定公共接口。HTML 按源码与渲染输入指纹精确复用，分析快照按 Lean 工具链、依赖锁和协议标识兼容复用。门户说明变更可直接复用原始 HTML。

  对象位于 `docs/quantum-atlas-ai/qatlib/tc/<toolchain>/`：

  ```text
  html/<fingerprint>.tar.gz
  html/<fingerprint>.json
  analysis/<compatible>/latest.tar.gz
  analysis/<compatible>/latest.json
  ```

  每份 JSON 只记录协议标识、输入指纹、兼容键和归档 SHA-256。归档按路径排序，固定 tar/gzip 时间为零、uid/gid 为零、用户名与组名为空，并统一文件权限。发布者须串行运行：先上传归档并回读校验，再更新 JSON；读取者在替换本地产物前校验兼容性、校验和与内容。两次写入之间的中断可能导致校验失败，重新发布完整快照即可修复。分析数据库通过 SQLite backup 保存已提交的 WAL 内容，与 `.doc` 分析标记共同归档；不带 HTML 渲染标记。仅在新分析归档缺失时，读取者可通过旧 `latest.json` 读取 `objects/<sha256>.tar.gz`；下次发布自然转为直存格式，不再写入旧对象路径。

  `DOCGEN_SRC=github` 和规范的 Git remote 决定源码仓库地址。锁定的 `doc-gen4` v4.35 仍将链接固定到构建提交，无法通过环境变量指定分支，因此发布分析前将 Qatlib 的 `source_url` 统一为公开仓库的 `main` 链接。恢复、裁剪和发布前，`assert_analysis_schema` 集中检查 `modules(name TEXT PRIMARY KEY, source_url TEXT)` 及依赖行的级联删除约定；不符合时给出明确升级提示。其余表与序列化数据仍交由 `doc-gen4` 自身校验。

  打包分析快照时，`.doc.trace` 及引用预处理的 `.trace` JSON 副本只保留 `schemaVersion` 和 `depHash`。Lake v4.35 对这些标记文件的命中检查使用依赖哈希与文件是否存在，`inputs` 和 `log` 缺省为空，`outputs` 缺省为空值；因此移除依赖路径说明与日志不会改变命中结果。本地 trace 保持原样；归档中的数据库、标记与 HTML 仍须全部通过严格的发布内容检查。

  升级 Lean 或 `doc-gen4` 时，核对 `lakefile.lean` 的 `srcUri.github`、`DocGen4/DB/Schema.lean`、`Lake/Build/Common.lean` 的 `BuildMetadata` 解析与标记命中检查、`.doc`/渲染标记约定及本脚本的 schema 断言；运行 `python3 scripts/test_docs_pipeline.py`，验证冷启动、增量恢复、已删除模块清理和最终源码链接。若协议语义不再兼容，更新 `FORMAT` 并重建分析；仅迁移存储布局或移除 trace 诊断字段时保留兼容键，以便接续已有分析成果。
