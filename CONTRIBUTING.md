# 贡献指南

> 🌐 [English version](./CONTRIBUTING.en.md)

欢迎通过 Issue 与 Pull Request 参与 `Qatlib` 的开发与完善。如计划新增较大规模的模块或重构已有基础定义，建议先开 Issue 讨论设计方案。

## 开发环境准备

1. 安装 [Lean 4 (`elan`)](https://lean-lang.org/lean4/doc/quickstart.html)。
2. 克隆仓库并拉取依赖缓存：

```bash
git clone https://github.com/quantum-atlas-ai/qatlib.git
cd qatlib

# 拉取上游 Mathlib / Physlib 及 Qatlib 预编译缓存（推荐）
lake exe get_cache
```

3. 构建你所修改的模块：

```bash
lake build Qatlib.Foundations.ChannelTheory.ChoiKraus
```

## 代码与证明规范

- **定位合适层级（单向依赖 `Foundations ← Concepts ← Papers`）**：
  - 通用线性代数、算子范数、CPTP 量子信道、测量与执行模型放入 `Qatlib/Foundations/`（不依赖 `Concepts` 或 `Papers`）；
  - 跨论文复用的算法原语（如块编码、QSVT/QSP、振幅放大、量子游走、对手下界等）放入 `Qatlib/Concepts/`（不依赖 `Papers`）；
  - 具体学术论文的定理与复杂度界放入 `Qatlib/Papers/`。
- **最小化 `import` 范围**：各具体模块应只 `import` 实际依赖的上游文件，不在库内普通文件中直接 `import Qatlib` 总入口，以免增大编译依赖扇出。
- **文档注释**：每个模块文件顶部需包含 `/-! ... -/` 模块说明，公共定义（`def` / `structure`）与主定理（`theorem` / `lemma`）需附带清晰的 `/-- ... -/` 数学文档注释。
- **完整证明与零警告**：合入主分支的代码禁止包含 `sorry`/`admit`、`native_decide`、`debug.skipKernelTC`、自定义 `axiom`（仅允许 Lean 标准公理 `propext`、`Quot.sound`、`Classical.choice`）或文件级 `set_option warningAsError false`，且全库默认启用 `autoImplicit = false`。
- **陈述忠实度（Statement Fidelity）**：`Qatlib/Papers/` 中的定理必须忠实反映原论文的隐含前提（例如欧氏 $\ell_2$ 范数、归一化概率分布、受实际执行轨迹约束的查询/门复杂度），不得用未受约束的结构体字段构造空洞结论，也不得将未证明的 `Prop` 定义命名为已证定理（若仅登记开放问题或规格说明，须以 `_statement` / `Spec` 结尾并在文档开头明确标注）。
- **外部代码来源说明**：若 PR 中移植或改编自其他开源项目或代码库，必须在根目录 `NOTICE`、对应文件头（保留原版权声明并注明上游仓库与 commit）及 PR 描述中完整披露。

## 提交 Pull Request 前的自检

```bash
# 1. 零警告编译受影响的模块
lake --wfail build <YourModule>

# 2. 运行静态风格、模块导入、语义忠实度检查，并验证内核公理合规
lake lint
lake test
```

## 开源协议

提交代码即表示你同意所贡献的内容按仓库根目录的 [Apache License 2.0](./LICENSE) 协议发布。
