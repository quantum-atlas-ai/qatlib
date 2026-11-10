# 库架构与模块设计

> 🌐 [English version](./architecture.en.md)

## 1. 分层依赖结构

`Qatlib` 的模块树位于 [`Qatlib/`](../Qatlib) 下，按单向依赖与复用角色自底向上分为三层（`Foundations ← Concepts ← Papers`，由 `lake lint` 强制校验）：

1. **[`Qatlib/Foundations/`](../Qatlib/Foundations)（底层数学结构与基础语义层）**
   提供全库共享的底层数学工具与基础语义，不依赖 `Concepts` 或 `Papers`：
   - 矩阵分析与算子范数（算子范数、迹范数、Schatten 范数、正半定矩阵序与混合态保真度）；
   - 概率统计与集中不等式、图结构与拉普拉斯算子、素性与群阶基础；
   - 有限精度算术、位字编码与数值误差传播、时间演化基础算子。

2. **[`Qatlib/Concepts/`](../Qatlib/Concepts)（可复用专题理论、算法框架与分析接口层）**
   构建在 `Foundations` 之上，沉淀专题理论、通用算法原语、复杂性下界与执行记账框架（部分源自文献但具备通用复用价值的理论也归入此层），包括：
   - 量子信道（CPTP、Stinespring、Choi–Kraus）、量子熵、纠缠与测量仪器、量子-经典协同执行语义（`Execution`）与资源记账（`ResourceBounds`）；
   - 块编码（`BlockEncoding`）、量子信号处理（`QspSimulation`、`SignalPrimitive`）与量子奇异值变换（`QsvtCore`、`QsvtLinearSolve`、`HhlAlgorithms`）；
   - 线性组合酉算子（LCU）、振幅放大与振幅估计（`AmplitudeCore`、`AmplitudeSearch`）、周期采样与隐藏子群恢复（`PeriodSampling`、`HspRecovery`、`AbelianDecoders`）；
   - 量子游走框架（`WalkSearch`）、多项式度数方法（`QueryComplexity`）与对手下界（`AdversaryBounds`）；
   - 费米子代数（`FermionAlgebra`）、玻色 Fock 空间（`BosonFock`）、张量网络（`TensorNetwork`）、编码与解码（`CodingDecoding`）以及半正定规划对偶与求解器（`SdpDuality`、`SdpMmwSolver`）。

3. **[`Qatlib/Papers/`](../Qatlib/Papers)（文献选定结果与资源分析层）**
   基于 `Foundations` 与 `Concepts` 的公共接口，按论文目录（`<TopicOrAuthor><YY>`，如 `GroverSearch96`、`SolovayKitaev05`、`QSingValue19`、`ClassShadows20`、`ECDLPResource17`）组织各文献中的特定模型定义、技术引理、主定理（通常位于 `MainResults/` 子目录）以及端到端资源复杂度界。

## 2. 模块组织与命名约定

为了在大型形式化库中保持清晰的命名空间与较小的编译扇出，目录与模块遵循以下组织规范：

- **严格 `UpperCamelCase` 模块路径**：所有目录与 `.lean` 文件名均采用大驼峰命名（如 `Qatlib/Concepts/QsvtCore/`、`Qatlib/Papers/GroverSearch96/`），不包含下划线或编号前缀。
- **定义与证明按主题拆分**：在多文件子目录中，核心数据结构与模型定义通常置于 `Defs.lean`、`*Defs.lean` 或 `Basic.lean` 中，专题引理按数学子主题拆分为独立模块，论文的核心结论定理汇总于 `MainResults/` 子目录下，避免单文件过大。
- **按需导入叶模块**：`Qatlib.Foundations`、`Qatlib.Concepts`、`Qatlib.Papers` 为目录层级前缀；库内与下游模块推荐按需精确导入具体叶模块（如 `import Qatlib.Papers.GroverSearch96.MainResults.GainConvergence`），仅在需要全库符号时导入顶层聚合入口 `import Qatlib`。
