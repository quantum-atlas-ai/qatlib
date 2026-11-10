# 快速开始与缓存指南

> 🌐 [English version](./getting-started.en.md)

本文档介绍如何安装 Lean 4 工具链、将 `Qatlib` 作为下游依赖引入、在本地拉取三层预编译缓存进行增量开发，以及排查常见的构建与编辑器问题。

## 1. 环境准备

1. **安装 `elan`（Lean 4 版本管理器）**：
   参考 [Lean 4 官方快速开始](https://lean-lang.org/lean4/doc/quickstart.html) 安装 `elan`。进入仓库目录时，`elan` 会自动根据 [`lean-toolchain`](../lean-toolchain) 下载并切换到对应的工具链版本（`leanprover/lean4:v4.35.0`）。
2. **推荐硬件配置**：
   - 若使用 `lake exe get_cache` 拉取预编译缓存：建议预留 **15 GB** 以上磁盘空间与 **8 GB+** 内存；
   - 若不使用缓存从零全量编译：建议 **16 GB+** 内存与多核 CPU。

## 2. 作为下游依赖使用

在你的 Lean 4 项目（需使用相同的 [`lean-toolchain`](../lean-toolchain) `leanprover/lean4:v4.35.0`）的 `lakefile.toml` 中添加：

```toml
[[require]]
name = "Qatlib"
git = "https://github.com/quantum-atlas-ai/qatlib.git"
rev = "v4.35.0"
```

在下游项目根目录运行以下命令，即可一次性拉取 `Mathlib`、`Physlib` 与 `Qatlib` 三层预编译缓存，无需在本地重新编译 `Qatlib`：

```bash
lake update
lake exe get_cache
```

随后在 `.lean` 文件中导入总入口或按需导入具体模块（建议在大型项目中按需导入具体子模块，以保持最小的编译依赖集）：

```lean
import Qatlib.Foundations.ChannelTheory.ChoiKraus
import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow
import Qatlib.Papers.GroverSearch96.MainResults.GainConvergence
```

## 3. 本地开发、三层缓存与按需构建

### 3.1 克隆仓库并拉取缓存

```bash
git clone https://github.com/quantum-atlas-ai/qatlib.git
cd qatlib

# 拉取三层预编译缓存
lake exe get_cache
```

`lake exe get_cache`（源码见 [`scripts/get_cache.lean`](../scripts/get_cache.lean)）会自动按顺序执行三步：
1. **`[1/3] Mathlib 缓存`**：调用 `lake exe cache get` 拉取 `Mathlib` 及其上游基础包（`Batteries`、`Aesop`、`Qq` 等）的 `.olean` 缓存；
2. **`[2/3] Physlib 缓存`**：读取 `.lake/packages/Physlib/lake-cache.toml`，调用 `lake cache get Physlib` 拉取上游 `Physlib` / `QuantumInfo` 缓存；
3. **`[3/3] Qatlib 缓存`**：读取 [`lake-cache.toml`](../lake-cache.toml)（公开只读端点 `https://lake-cache.quantum-atlas.ai`），调用 `lake cache get Qatlib` 将预编译构件恢复到本地缓存与 `.lake/build/`。

### 3.2 按需构建与统一静态审计

拉取缓存后，`lake build` 只会增量编译你修改过的文件及其下游依赖：

```bash
# 编译单个模块（推荐日常开发使用）
lake build Qatlib.Foundations.ChannelTheory.ChoiKraus
lake build Qatlib.Papers.GroverSearch96.MainResults.GainConvergence

# 编译全库
lake build Qatlib

# 运行秒级代码风格与模块导入检查（不加载编译环境）
lake lint

# 运行内核级零 sorryAx 与标准公理集验证（加载已编译的 .olean 环境）
lake test
```

## 4. VS Code 编辑器配置与常见问题排查

1. **必须打开仓库根目录**：
   在 VS Code 中安装官方 [Lean 4 扩展](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) 后，请务必通过 **File → Open Folder** 打开 `qatlib` **根目录**（不要单独打开 `Qatlib/Papers` 等子目录，否则 Lake 无法读取根目录的 `lakefile.toml` 与 `lean-toolchain`）。
2. **编辑器内符号跳转与悬停提示**：
   本仓库在 [`lakefile.toml`](../lakefile.toml) 中默认启用了 `enableArtifactCache = true` 与 `restoreAllArtifacts = true`。运行 `lake exe get_cache` 后，VS Code 的 `lean --server` 会直接复用预编译的 `.olean` 与 `.ilean` 索引，无需等待漫长的后台重编即可获得完整的类型提示与跳转支持。
3. **常见缓存问题排查**：
   - 若切换分支或更新依赖后出现 `.olean` 版本不匹配报错，可先执行 `lake exe get_cache` 重新同步；
   - 若本地构建目录状态异常，可执行 `lake clean` 清理本地构建产物后再运行 `lake exe get_cache && lake build`。
