<div align="center">

<!-- Logo placeholder: <img src="./docs/qatlib-logo.svg" alt="Qatlib" width="640" /> -->

# Qatlib

**基于 Lean 4 的量子计算与量子信息形式化数学库**

[![Lint](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/lint.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/lint.yml)
[![Build](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/build.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/build.yml)
[![Cache](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/publish-cache.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/publish-cache.yml)
[![api_docs](https://img.shields.io/badge/doc-API_docs-blue)](https://quantum-atlas-ai.github.io/qatlib/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](./LICENSE)

[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)](https://github.com/leanprover-community/mathlib4)
[![Physlib](https://img.shields.io/badge/Physlib-v4.35.0-blue)](https://github.com/leanprover-community/physlib)

简体中文 ｜ [English](./README.en.md)

</div>

---

## <a id="overview"></a>简介

**Qatlib** 是面向量子计算与量子信息领域的 [Lean 4](https://lean-lang.org/) 形式化数学库，构建于 [`mathlib4`](https://github.com/leanprover-community/mathlib4) 与 [`Physlib`](https://github.com/leanprover-community/physlib) 之上。

项目旨在用统一的数学定义与算子代数接口，对量子计算中的基础数学结构、核心算法原语以及代表性学术文献中的定理与复杂度分析进行形式化。

## <a id="installation"></a>安装与使用

如尚未安装 Lean 4 与 `elan`，请先参考 [Lean 4 官方安装指南](https://lean-lang.org/lean4/doc/quickstart.html) 或 [mathlib4 安装说明](https://leanprover-community.github.io/get_started.html)。

### <a id="as-dependency"></a>作为下游依赖引入

请确保下游项目的 `lean-toolchain` 与本仓库一致（当前为 `leanprover/lean4:v4.35.0`），并在 `lakefile.toml` 中添加：

```toml
[[require]]
name = "Qatlib"
git = "https://github.com/quantum-atlas-ai/qatlib.git"
rev = "main" # 跟踪最新合入定理（推荐）；若需固定在工具链发布基线可填 "v4.35.0"
```

首次引入（或后续需要同步上游最新合入定理时），依次运行以下两条命令以更新源码锁文件（`lake-manifest.json`）并拉取三层预编译缓存（`Mathlib` + `Physlib` + `Qatlib`），无需在本地从头编译 `Qatlib`：

```bash
lake update
lake exe get_cache
```

> **提示**：Lake 通过 `lake-manifest.json` 锁定具体 Commit。日常开发中只要不主动运行 `lake update`，上游 `main` 分支的更新不会影响你本地的构建状态；当你运行 `lake update`（或 `lake update Qatlib`）拉取上游新定理后，请配套执行一次 `lake exe get_cache` 下载对应的预编译缓存。

随后即可在 `.lean` 文件中导入总入口或按需导入具体子模块：

```lean
import Qatlib
```

### <a id="local-development"></a>本地开发与构建

```bash
git clone https://github.com/quantum-atlas-ai/qatlib.git
cd qatlib

# 1. 一键拉取 Mathlib、Physlib 与 Qatlib 预编译缓存（推荐，大幅加速首次构建）
lake exe get_cache

# 2. 编译全库或按需编译指定模块（仅增量重编改动文件及其下游依赖）
lake build Qatlib
lake build Qatlib.Papers.GroverSearch96.MainResults.GainConvergence

# 3. 运行静态代码风格与导入检查（秒级）及内核公理验证
lake lint
lake test
```

在 Visual Studio Code 中开发时，请通过 **File → Open Folder** 直接打开仓库根目录（切勿只打开子文件夹，以确保 Lean 4 扩展正确识别 `lean-toolchain`、`lakefile.toml` 与 `.lake` 缓存）。

## <a id="structure"></a>目录组织与涵盖领域

[`Qatlib/`](./Qatlib) 按依赖与复用角色自底向上组织为三层（单向依赖 `Foundations ← Concepts ← Papers`）：

- **[`Qatlib/Foundations/`](./Qatlib/Foundations)**：底层通用数学结构与基础语义（矩阵分析、算子范数、Schatten 范数、纯态与混合态代数、概率统计与集中不等式、图结构与拉普拉斯算子、有限精度算术与数值误差分析、时间演化基础）。
- **[`Qatlib/Concepts/`](./Qatlib/Concepts)**：可复用的专题理论、核心算法框架与复杂度分析接口（量子信道与量子熵、块编码、QSVT/QSP、LCU、振幅放大与估计、周期采样与隐藏子群恢复、量子游走、多项式度数界与对手下界、费米子/玻色子代数、编码与解码、执行语义与资源记账等）。
- **[`Qatlib/Papers/`](./Qatlib/Papers)**：按代表性文献组织的选定定义、引理、主定理与资源复杂度分析。

下表从研究主题角度提供内容导航（各方向存在交叉，所列目录为当前实现的代表性入口）：

| 领域 | 涵盖主题 | 代表性子目录 |
|---|---|---|
| **1. 量子计算模型、执行语义与资源记账** | 量子电路模型、量子图灵机、基于测量的量子计算（MBQC）、Solovay–Kitaev 编译、量子-经典协同执行、有限精度与经典磁带代价、以及 Query / Gate / Ancilla / Depth 资源记账 | [`Qatlib/Concepts/Execution/`](./Qatlib/Concepts/Execution)<br>[`Qatlib/Concepts/ResourceBounds/`](./Qatlib/Concepts/ResourceBounds)<br>[`Qatlib/Foundations/FinitePrecision/`](./Qatlib/Foundations/FinitePrecision)<br>[`Qatlib/Concepts/MbqcFlow/`](./Qatlib/Concepts/MbqcFlow)<br>[`Qatlib/Papers/QCircuitYao93/`](./Qatlib/Papers/QCircuitYao93)<br>[`Qatlib/Papers/SolovayKitaev05/`](./Qatlib/Papers/SolovayKitaev05) |
| **2. 量子信息论、信道、纠缠、层析与精密测量** | CPTP 量子信道、Stinespring 扩张、Choi–Kraus 表示、量子熵与相对熵、纠缠判据与 LOCC、经典影子与多观测量估计（Classical Shadows）、量子精密测量 | [`Qatlib/Concepts/ChannelTheory/`](./Qatlib/Concepts/ChannelTheory)<br>[`Qatlib/Concepts/QuantumEntropy/`](./Qatlib/Concepts/QuantumEntropy)<br>[`Qatlib/Concepts/Entanglement/`](./Qatlib/Concepts/Entanglement)<br>[`Qatlib/Concepts/ShadowModels/`](./Qatlib/Concepts/ShadowModels)<br>[`Qatlib/Papers/ClassShadows20/`](./Qatlib/Papers/ClassShadows20)<br>[`Qatlib/Papers/QuantumMetro05/`](./Qatlib/Papers/QuantumMetro05) |
| **3. 量子搜索、量子游走与查询复杂度上下界** | Grover 搜索、振幅放大与估计、固定点搜索、Szegedy / Ambainis 离散与连续量子游走、元素互异性、多项式度数方法、对手下界（Adversary Method）与 Span Program | [`Qatlib/Concepts/AmplitudeSearch/`](./Qatlib/Concepts/AmplitudeSearch)<br>[`Qatlib/Concepts/QueryComplexity/`](./Qatlib/Concepts/QueryComplexity)<br>[`Qatlib/Concepts/AdversaryBounds/`](./Qatlib/Concepts/AdversaryBounds)<br>[`Qatlib/Concepts/WalkSearch/`](./Qatlib/Concepts/WalkSearch)<br>[`Qatlib/Papers/GroverSearch96/`](./Qatlib/Papers/GroverSearch96)<br>[`Qatlib/Papers/SpanProgram07/`](./Qatlib/Papers/SpanProgram07) |
| **4. 代数、数论与密码分析量子算法** | QFT 与 Fourier 采样、Shor 大数分解与离散对数周期恢复、椭圆曲线离散对数（ECDLP）资源分析、阿贝尔与非阿贝尔隐藏子群问题（HSP）、Simon 解码与对称密码量子分析、格问题条件归约 | [`Qatlib/Concepts/PeriodSampling/`](./Qatlib/Concepts/PeriodSampling)<br>[`Qatlib/Concepts/CurveGroups/`](./Qatlib/Concepts/CurveGroups)<br>[`Qatlib/Concepts/HspRecovery/`](./Qatlib/Concepts/HspRecovery)<br>[`Qatlib/Concepts/AbelianDecoders/`](./Qatlib/Concepts/AbelianDecoders)<br>[`Qatlib/Papers/ECDLPResource17/`](./Qatlib/Papers/ECDLPResource17)<br>[`Qatlib/Papers/DihedralHSP04/`](./Qatlib/Papers/DihedralHSP04) |
| **5. 量子线性代数、块编码与 QSVT / QSP** | 块编码（Block-Encoding）代数、量子信号处理（QSP）、量子奇异值变换（QSVT）、量子化（Qubitization）、线性组合酉算子（LCU）、HHL 与量子线性方程组求解、矩阵函数逼近 | [`Qatlib/Concepts/BlockEncoding/`](./Qatlib/Concepts/BlockEncoding)<br>[`Qatlib/Concepts/QsvtCore/`](./Qatlib/Concepts/QsvtCore)<br>[`Qatlib/Concepts/QsvtLinearSolve/`](./Qatlib/Concepts/QsvtLinearSolve)<br>[`Qatlib/Concepts/HhlAlgorithms/`](./Qatlib/Concepts/HhlAlgorithms)<br>[`Qatlib/Concepts/SignalPrimitive/`](./Qatlib/Concepts/SignalPrimitive)<br>[`Qatlib/Papers/QSingValue19/`](./Qatlib/Papers/QSingValue19) |
| **6. 哈密顿量模拟、开放量子系统与科学计算** | Lie–Trotter–Suzuki 乘积公式与交换子误差界、截断泰勒级数、QSP 哈密顿量模拟、LCHS 线性微分方程模拟、qDRIFT 随机哈密顿量模拟、Lindblad 演化、量子 Gibbs 态制备与蒙特卡洛估计 | [`Qatlib/Concepts/TrotterFormula/`](./Qatlib/Concepts/TrotterFormula)<br>[`Qatlib/Concepts/QspSimulation/`](./Qatlib/Concepts/QspSimulation)<br>[`Qatlib/Concepts/LchsSimulation/`](./Qatlib/Concepts/LchsSimulation)<br>[`Qatlib/Concepts/LindbladFlow/`](./Qatlib/Concepts/LindbladFlow)<br>[`Qatlib/Concepts/QuantumGibbs/`](./Qatlib/Concepts/QuantumGibbs)<br>[`Qatlib/Papers/TrotterError19/`](./Qatlib/Papers/TrotterError19) |
| **7. 多体物理、量子化学、张量网络与量子纠错** | Jordan–Wigner 与 Bravyi–Kitaev 费米子映射、玻色 Fock 空间、量子化学模拟与表面码资源估算、张量网络、稳定子码与 CSS 码解码器 | [`Qatlib/Concepts/FermionAlgebra/`](./Qatlib/Concepts/FermionAlgebra)<br>[`Qatlib/Concepts/BosonFock/`](./Qatlib/Concepts/BosonFock)<br>[`Qatlib/Concepts/TensorNetwork/`](./Qatlib/Concepts/TensorNetwork)<br>[`Qatlib/Concepts/CodingDecoding/`](./Qatlib/Concepts/CodingDecoding)<br>[`Qatlib/Papers/BKFermion17/`](./Qatlib/Papers/BKFermion17)<br>[`Qatlib/Papers/QChemistry14/`](./Qatlib/Papers/QChemistry14) |
| **8. 量子优化、量子机器学习与复杂性理论** | 绝热量子计算与能隙分析、QAOA 与 Overlap Gap 性质、量子半正定规划（SDP）求解器、局域哈密顿量与 QMA 完全性、量子主成分分析（qPCA）与变分电路可训练性分析 | [`Qatlib/Concepts/SdpDuality/`](./Qatlib/Concepts/SdpDuality)<br>[`Qatlib/Concepts/SdpMmwSolver/`](./Qatlib/Concepts/SdpMmwSolver)<br>[`Qatlib/Concepts/QmaCompleteness/`](./Qatlib/Concepts/QmaCompleteness)<br>[`Qatlib/Papers/SDPBrandao16/`](./Qatlib/Papers/SDPBrandao16)<br>[`Qatlib/Papers/QAOAScaling23/`](./Qatlib/Papers/QAOAScaling23)<br>[`Qatlib/Papers/Trainability23/`](./Qatlib/Papers/Trainability23) |

详细模块组织与命名约定参见 [`docs/architecture.md`](./docs/architecture.md)。

## <a id="documentation"></a>文档与工具索引

- **[快速上手与缓存指南 (`docs/getting-started.md`)](./docs/getting-started.md)**：环境准备（`elan` 与 VS Code 配置）、三层缓存拉取机制（`lake-cache.toml`）、按需导入与增量构建说明。
- **[库架构与模块设计 (`docs/architecture.md`)](./docs/architecture.md)**：`Foundations / Concepts / Papers` 目录划分与模块命名约定。
- **[开发脚本与检查工具说明 (`scripts/README.md`)](./scripts/README.md)**：缓存拉取工具 `lake exe get_cache`、静态风格与导入检查器 `lake lint` 以及内核级零 `sorryAx` / 标准公理集验证器 `lake test` 详细说明。
- **API 参考文档（`doc-gen4`）**：与 `mathlib4` 及 `Physlib` 一致，使用 Lean 4 官方 [`doc-gen4`](https://github.com/leanprover/doc-gen4) 生成全库 API 索引（构建工作流见 [`.github/workflows/docs.yml`](./.github/workflows/docs.yml)）。

## <a id="contributing"></a>参与贡献

欢迎通过 Issue 或 Pull Request 参与贡献。提交流程、代码风格与模块编写约定请阅读 [`CONTRIBUTING.md`](./CONTRIBUTING.md)（[English](./CONTRIBUTING.en.md)）。

## <a id="citation"></a>引用与协议

如果你在研究中使用了 Qatlib，欢迎引用本项目：

```bibtex
@software{qatlib,
  author  = {{Qatlib Contributors}},
  title   = {{Qatlib: The Lean Library for Formalized Quantum Computing and Quantum Information}},
  license = {Apache-2.0},
  url     = {https://github.com/quantum-atlas-ai/qatlib}
}
```

本项目采用 [Apache License 2.0](./LICENSE) 开源协议。
