<div align="center">

<img src="./.github/assets/qatlib-wordmark.svg" alt="Qatlib" width="560" />

**The Lean Library for Formalized Quantum Computing and Quantum Information**

[![Lint](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/lint.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/lint.yml)
[![Build](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/build.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/build.yml)
[![Cache](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/publish-cache.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/publish-cache.yml)
[![api_docs](https://img.shields.io/badge/doc-API_docs-blue)](https://quantum-atlas-ai.github.io/qatlib/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](./LICENSE)

[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)](https://github.com/leanprover-community/mathlib4)
[![Physlib](https://img.shields.io/badge/Physlib-v4.35.0-blue)](https://github.com/leanprover-community/physlib)

[简体中文](./README.md) ｜ English

</div>

---

## <a id="overview"></a>Overview

**Qatlib** is a formal library for quantum computing and quantum information in the [Lean 4 theorem prover](https://lean-lang.org/), built on top of [`mathlib4`](https://github.com/leanprover-community/mathlib4) and [`Physlib`](https://github.com/leanprover-community/physlib).

It provides unified mathematical definitions, operator-algebraic interfaces, reusable algorithmic primitives, and formalized theorems from the quantum computing literature.

## <a id="installation"></a>Installation & Usage

If you do not have Lean 4 and `elan` installed yet, follow the [official Lean 4 quickstart](https://lean-lang.org/lean4/doc/quickstart.html) or the [mathlib4 installation guide](https://leanprover-community.github.io/get_started.html).

### <a id="as-dependency"></a>Using `Qatlib` as a Dependency

Ensure your project's `lean-toolchain` matches this repository (`leanprover/lean4:v4.35.0`), and add `Qatlib` to your `lakefile.toml`:

```toml
[[require]]
name = "Qatlib"
git = "https://github.com/quantum-atlas-ai/qatlib.git"
rev = "main" # Track the latest theorems (recommended); or pin to "v4.35.0" for the initial toolchain baseline
```

When adding the dependency for the first time (or when pulling newly added upstream theorems), run both commands below to update `lake-manifest.json` and fetch the prebuilt caches (`Mathlib` + `Physlib` + `Qatlib`):

```bash
lake update
lake exe get_cache
```

> **Note**: Lake locks the exact Git commit SHA in `lake-manifest.json`. Upstream commits on `main` will not affect your local build unless you explicitly run `lake update` (or `lake update Qatlib`). Whenever you run `lake update`, follow it with `lake exe get_cache` to fetch the corresponding prebuilt caches.

Then import `Qatlib` (or specific submodules) in your `.lean` files:

```lean
import Qatlib
```

### <a id="local-development"></a>Local Development & Building

```bash
git clone https://github.com/quantum-atlas-ai/qatlib.git
cd qatlib

# 1. Fetch prebuilt Mathlib, Physlib, and Qatlib caches (recommended)
lake exe get_cache

# 2. Build the entire library or a specific module (incremental)
lake build Qatlib
lake build Qatlib.Papers.GroverSearch96.MainResults.GainConvergence

# 3. Run static style & import checks (~1s) and kernel axiom verification
lake lint
lake test
```

When working in Visual Studio Code, open the top-level `qatlib` directory (**File → Open Folder**) rather than a subdirectory so the Lean 4 extension locates `lean-toolchain`, `lakefile.toml`, and `.lake`.

## <a id="structure"></a>Repository Structure & Topics Covered

[`Qatlib/`](./Qatlib) is organized bottom-up into three layers by dependency and reuse role (strictly one-way `Foundations ← Concepts ← Papers`):

- **[`Qatlib/Foundations/`](./Qatlib/Foundations)**: Shared mathematical structures and core semantics (matrix analysis, operator and Schatten norms, pure and mixed state algebra, probability and concentration inequalities, graph Laplacians, finite-precision arithmetic and numerical error bounds, time-evolution foundations).
- **[`Qatlib/Concepts/`](./Qatlib/Concepts)**: Reusable domain theories, algorithmic frameworks, and complexity interfaces (quantum channels and entropy, block-encoding algebra, QSVT/QSP, LCU, amplitude amplification and estimation, period sampling and HSP recovery, quantum walks, polynomial degree and adversary lower bounds, fermionic/bosonic algebras, coding and decoding, execution semantics, and resource accounting).
- **[`Qatlib/Papers/`](./Qatlib/Papers)**: Selected definitions, lemmas, main theorems, and resource complexity analyses organized by research paper.

The table below provides a thematic navigation across eight interconnected areas, with representative entry directories:

| Area | Topics | Representative Directories |
|---|---|---|
| **1. Quantum Computation Models, Execution Semantics & Resource Accounting** | Quantum circuit model, quantum Turing machines, measurement-based quantum computation (MBQC), Solovay–Kitaev compilation, hybrid quantum-classical execution, finite-precision and classical tape costs, and query/gate/ancilla/depth accounting | [`Qatlib/Concepts/Execution/`](./Qatlib/Concepts/Execution)<br>[`Qatlib/Concepts/ResourceBounds/`](./Qatlib/Concepts/ResourceBounds)<br>[`Qatlib/Foundations/FinitePrecision/`](./Qatlib/Foundations/FinitePrecision)<br>[`Qatlib/Concepts/MbqcFlow/`](./Qatlib/Concepts/MbqcFlow)<br>[`Qatlib/Papers/QCircuitYao93/`](./Qatlib/Papers/QCircuitYao93)<br>[`Qatlib/Papers/SolovayKitaev05/`](./Qatlib/Papers/SolovayKitaev05) |
| **2. Quantum Information, Channels, Entanglement, Tomography & Metrology** | CPTP quantum channels, Stinespring dilation, Choi–Kraus representation, von Neumann and relative entropy, entanglement criteria and LOCC, classical shadows and multi-observable estimation, and quantum metrology | [`Qatlib/Concepts/ChannelTheory/`](./Qatlib/Concepts/ChannelTheory)<br>[`Qatlib/Concepts/QuantumEntropy/`](./Qatlib/Concepts/QuantumEntropy)<br>[`Qatlib/Concepts/Entanglement/`](./Qatlib/Concepts/Entanglement)<br>[`Qatlib/Concepts/ShadowModels/`](./Qatlib/Concepts/ShadowModels)<br>[`Qatlib/Papers/ClassShadows20/`](./Qatlib/Papers/ClassShadows20)<br>[`Qatlib/Papers/QuantumMetro05/`](./Qatlib/Papers/QuantumMetro05) |
| **3. Quantum Search, Quantum Walks & Query Complexity Upper and Lower Bounds** | Grover search, amplitude amplification and estimation, fixed-point search, Szegedy and Ambainis discrete/continuous quantum walks, element distinctness, polynomial degree method, adversary lower bounds, and span programs | [`Qatlib/Concepts/AmplitudeSearch/`](./Qatlib/Concepts/AmplitudeSearch)<br>[`Qatlib/Concepts/QueryComplexity/`](./Qatlib/Concepts/QueryComplexity)<br>[`Qatlib/Concepts/AdversaryBounds/`](./Qatlib/Concepts/AdversaryBounds)<br>[`Qatlib/Concepts/WalkSearch/`](./Qatlib/Concepts/WalkSearch)<br>[`Qatlib/Papers/GroverSearch96/`](./Qatlib/Papers/GroverSearch96)<br>[`Qatlib/Papers/SpanProgram07/`](./Qatlib/Papers/SpanProgram07) |
| **4. Algebraic, Number-Theoretic & Cryptanalytic Quantum Algorithms** | QFT and Fourier sampling, Shor's factoring and discrete-log period recovery, elliptic-curve discrete logarithm (ECDLP) resource estimates, abelian and non-abelian hidden subgroup problems (HSP), Simon decoding and symmetric cryptanalysis, conditional lattice reductions | [`Qatlib/Concepts/PeriodSampling/`](./Qatlib/Concepts/PeriodSampling)<br>[`Qatlib/Concepts/CurveGroups/`](./Qatlib/Concepts/CurveGroups)<br>[`Qatlib/Concepts/HspRecovery/`](./Qatlib/Concepts/HspRecovery)<br>[`Qatlib/Concepts/AbelianDecoders/`](./Qatlib/Concepts/AbelianDecoders)<br>[`Qatlib/Papers/ECDLPResource17/`](./Qatlib/Papers/ECDLPResource17)<br>[`Qatlib/Papers/DihedralHSP04/`](./Qatlib/Papers/DihedralHSP04) |
| **5. Quantum Linear Algebra, Block-Encoding & QSVT / QSP** | Block-encoding algebra, quantum signal processing (QSP), quantum singular value transformation (QSVT), qubitization, linear combination of unitaries (LCU), HHL and quantum linear systems, and matrix function approximation | [`Qatlib/Concepts/BlockEncoding/`](./Qatlib/Concepts/BlockEncoding)<br>[`Qatlib/Concepts/QsvtCore/`](./Qatlib/Concepts/QsvtCore)<br>[`Qatlib/Concepts/QsvtLinearSolve/`](./Qatlib/Concepts/QsvtLinearSolve)<br>[`Qatlib/Concepts/HhlAlgorithms/`](./Qatlib/Concepts/HhlAlgorithms)<br>[`Qatlib/Concepts/SignalPrimitive/`](./Qatlib/Concepts/SignalPrimitive)<br>[`Qatlib/Papers/QSingValue19/`](./Qatlib/Papers/QSingValue19) |
| **6. Hamiltonian Simulation, Open Systems & Scientific Computing** | Lie–Trotter–Suzuki product formulas and commutator error bounds, truncated Taylor series, QSP Hamiltonian simulation, LCHS linear differential equation simulation, qDRIFT randomized Hamiltonian simulation, Lindblad evolution, quantum Gibbs sampling, and Monte Carlo estimation | [`Qatlib/Concepts/TrotterFormula/`](./Qatlib/Concepts/TrotterFormula)<br>[`Qatlib/Concepts/QspSimulation/`](./Qatlib/Concepts/QspSimulation)<br>[`Qatlib/Concepts/LchsSimulation/`](./Qatlib/Concepts/LchsSimulation)<br>[`Qatlib/Concepts/LindbladFlow/`](./Qatlib/Concepts/LindbladFlow)<br>[`Qatlib/Concepts/QuantumGibbs/`](./Qatlib/Concepts/QuantumGibbs)<br>[`Qatlib/Papers/TrotterError19/`](./Qatlib/Papers/TrotterError19) |
| **7. Many-Body Physics, Quantum Chemistry, Tensor Networks & QEC** | Jordan–Wigner and Bravyi–Kitaev fermionic mappings, bosonic Fock spaces, quantum chemistry simulation and surface-code resource estimation, tensor networks, stabilizer and CSS code decoders | [`Qatlib/Concepts/FermionAlgebra/`](./Qatlib/Concepts/FermionAlgebra)<br>[`Qatlib/Concepts/BosonFock/`](./Qatlib/Concepts/BosonFock)<br>[`Qatlib/Concepts/TensorNetwork/`](./Qatlib/Concepts/TensorNetwork)<br>[`Qatlib/Concepts/CodingDecoding/`](./Qatlib/Concepts/CodingDecoding)<br>[`Qatlib/Papers/BKFermion17/`](./Qatlib/Papers/BKFermion17)<br>[`Qatlib/Papers/QChemistry14/`](./Qatlib/Papers/QChemistry14) |
| **8. Quantum Optimization, Quantum Machine Learning & Complexity** | Adiabatic quantum computation and spectral gap bounds, QAOA and the Overlap Gap Property, quantum semidefinite programming (SDP) solvers, local Hamiltonians and QMA completeness, quantum PCA, and variational circuit trainability | [`Qatlib/Concepts/SdpDuality/`](./Qatlib/Concepts/SdpDuality)<br>[`Qatlib/Concepts/SdpMmwSolver/`](./Qatlib/Concepts/SdpMmwSolver)<br>[`Qatlib/Concepts/QmaCompleteness/`](./Qatlib/Concepts/QmaCompleteness)<br>[`Qatlib/Papers/SDPBrandao16/`](./Qatlib/Papers/SDPBrandao16)<br>[`Qatlib/Papers/QAOAScaling23/`](./Qatlib/Papers/QAOAScaling23)<br>[`Qatlib/Papers/Trainability23/`](./Qatlib/Papers/Trainability23) |

See [`docs/architecture.en.md`](./docs/architecture.en.md) for a detailed module overview.

## <a id="documentation"></a>Documentation & Tooling

- **[Getting Started & Cache Guide (`docs/getting-started.en.md`)](./docs/getting-started.en.md)**: Toolchain setup (`elan` and VS Code), three-tier cache architecture (`lake-cache.toml`), targeted imports, and incremental builds.
- **[Library Architecture & Module Overview (`docs/architecture.en.md`)](./docs/architecture.en.md)**: The `Foundations / Concepts / Papers` directory layout and module naming conventions.
- **[Scripts, Linter & Test Reference (`scripts/README.en.md`)](./scripts/README.en.md)**: Details on `lake exe get_cache`, the static style/import linter `lake lint`, and the kernel-level zero-`sorryAx` / standard-axiom verifier `lake test`.
- **API Reference (`doc-gen4`)**: Following `mathlib4` and `Physlib`, API documentation is built using Lean 4's official [`doc-gen4`](https://github.com/leanprover/doc-gen4) (configured in [`.github/workflows/docs.yml`](./.github/workflows/docs.yml)).

## <a id="contributing"></a>Contributing

Contributions via issues and pull requests are welcome. Please see [`CONTRIBUTING.en.md`](./CONTRIBUTING.en.md) ([中文版](./CONTRIBUTING.md)) for development workflow and style conventions.

## <a id="citation"></a>Citation & License

If you use Qatlib in your research, please cite:

```bibtex
@software{qatlib,
  author  = {{Qatlib Contributors}},
  title   = {{Qatlib: The Lean Library for Formalized Quantum Computing and Quantum Information}},
  license = {Apache-2.0},
  url     = {https://github.com/quantum-atlas-ai/qatlib}
}
```

Licensed under the [Apache License 2.0](./LICENSE).
