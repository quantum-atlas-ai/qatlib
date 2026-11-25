<div align="center">

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="./.github/assets/qatlib-wordmark-dark.svg" />
  <source type="image/svg+xml" srcset="./.github/assets/qatlib-wordmark.svg" />
  <img src="./.github/assets/qatlib-wordmark.png" alt="Qatlib" width="360" height="87" />
</picture>

**The Lean 4 Library for Quantum Computing and Quantum Information**

[![Lint](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/lint.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/lint.yml)
[![Build](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/build.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/build.yml)
[![Cache](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/publish-cache.yml/badge.svg)](https://github.com/quantum-atlas-ai/qatlib/actions/workflows/publish-cache.yml)
[![api_docs](https://img.shields.io/badge/doc-API_docs-blue)](https://quantum-atlas-ai.github.io/qatlib/en/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](./LICENSE)

[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)](https://github.com/leanprover-community/mathlib4)
[![Physlib](https://img.shields.io/badge/Physlib-v4.35.0-blue)](https://github.com/leanprover-community/physlib)

[简体中文](./README.md) ｜ English

[Theorem Dependency Star Fields (2D / 3D)](https://quantum-atlas-ai.github.io/qatlib/en/dependencies.html)

</div>

---

## <a id="overview"></a>Overview

**Qatlib** is a [Lean 4](https://lean-lang.org/) library for quantum computing and quantum information, built on [`mathlib4`](https://github.com/leanprover-community/mathlib4) and [`Physlib`](https://github.com/leanprover-community/physlib).

It formalizes mathematical foundations, reusable algorithmic primitives, and theorems and resource bounds from the literature.

### <a id="status-provenance"></a>Status, Scope & Provenance

- **Kernel soundness guarantee**: Every merged module passes Lean 4 kernel-environment auditing ([`lake test`](./scripts/test.lean)), ensuring its transitive axiom closure lies strictly within Lean's three standard axioms `{propext, Classical.choice, Quot.sound}` (`0 sorryAx`, no `native_decide`, no custom axioms), complemented by static source-fidelity checks ([`scripts/lint.lean`](./scripts/lint.lean)).
- **Paper formalization scope**: Directories under `Qatlib/Papers/` span varying formalization depths—ranging from full end-to-end main theorems and query/gate complexity bounds to targeted lemmas, conditional reductions, parameter analyses, or premise corrections and counterexamples (documented in each module's `/-! ... -/` header). To report a discrepancy between a formalized statement and its source paper, please open a [**Statement Fidelity Report**](./.github/ISSUE_TEMPLATE/statement_fidelity.md).
- **AI-assisted provenance**: Formalizations and refactorings in Qatlib are developed with substantial AI-agent assistance, verified by the Lean 4 kernel, automated static/semantic linters, and targeted human mathematical review.
- **Third-party acknowledgments**: Selected complex-analysis and polynomial-approximation components under `Qatlib/Foundations/CbmdAnalysis/` are adapted from [TauCeti](https://github.com/TauCetiProject/TauCeti) and [CausalSmith / Causalean](https://github.com/Jiyuan-Tan/CausalSmith) under Apache-2.0; full provenance and upstream commit SHAs are recorded in [`NOTICE`](./NOTICE).

## <a id="installation"></a>Installation & Usage

If you do not have Lean 4 and `elan` installed yet, follow the [official Lean 4 quickstart](https://lean-lang.org/lean4/doc/quickstart.html) or the [mathlib4 installation guide](https://leanprover-community.github.io/get_started.html).

### <a id="as-dependency"></a>Using `Qatlib` as a Dependency

Ensure your project's `lean-toolchain` matches this repository (`leanprover/lean4:v4.35.0`), and add `Qatlib` to your `lakefile.toml`:

```toml
[[require]]
name = "Qatlib"
git = "https://github.com/quantum-atlas-ai/qatlib.git"
rev = "main" # Track the latest theorems (recommended); or lock a specific commit SHA in lake-manifest.json (note: tag "v4.35.0" marks only the initial toolchain snapshot)
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

The table groups the library by research area and lists representative directories.

| Area | Topics | Representative Directories |
|---|---|---|
| **1. Quantum Computation Models, Execution Semantics & Resource Accounting** | Quantum circuit model, quantum Turing machines, measurement-based quantum computation (MBQC), Solovay–Kitaev compilation, hybrid quantum-classical execution, finite-precision and classical tape costs, and query/gate/ancilla/depth accounting | [`Qatlib/Concepts/Execution/`](./Qatlib/Concepts/Execution)<br>[`Qatlib/Concepts/ResourceBounds/`](./Qatlib/Concepts/ResourceBounds)<br>[`Qatlib/Foundations/FinitePrecision/`](./Qatlib/Foundations/FinitePrecision)<br>[`Qatlib/Concepts/MbqcFlow/`](./Qatlib/Concepts/MbqcFlow)<br>[`Qatlib/Papers/QCircuitYao93/`](./Qatlib/Papers/QCircuitYao93)<br>[`Qatlib/Papers/SolovayKitaev05/`](./Qatlib/Papers/SolovayKitaev05) |
| **2. Quantum Information, Channels, Entanglement, Tomography & Metrology** | CPTP quantum channels, Stinespring dilation, Choi–Kraus representation, von Neumann and relative entropy, entanglement criteria and LOCC, classical shadows and multi-observable estimation, and quantum metrology | [`Qatlib/Concepts/ChannelTheory/`](./Qatlib/Concepts/ChannelTheory)<br>[`Qatlib/Concepts/QuantumEntropy/`](./Qatlib/Concepts/QuantumEntropy)<br>[`Qatlib/Concepts/Entanglement/`](./Qatlib/Concepts/Entanglement)<br>[`Qatlib/Concepts/ShadowModels/`](./Qatlib/Concepts/ShadowModels)<br>[`Qatlib/Papers/ClassShadows20/`](./Qatlib/Papers/ClassShadows20)<br>[`Qatlib/Papers/QuantumMetro05/`](./Qatlib/Papers/QuantumMetro05) |
| **3. Quantum Search, Quantum Walks & Query Complexity Upper and Lower Bounds** | Grover search, amplitude amplification and estimation, fixed-point search, Szegedy and Ambainis discrete/continuous quantum walks, element distinctness, polynomial degree method, adversary lower bounds, and span programs | [`Qatlib/Concepts/AmplitudeSearch/`](./Qatlib/Concepts/AmplitudeSearch)<br>[`Qatlib/Concepts/QueryComplexity/`](./Qatlib/Concepts/QueryComplexity)<br>[`Qatlib/Concepts/AdversaryBounds/`](./Qatlib/Concepts/AdversaryBounds)<br>[`Qatlib/Concepts/WalkSearch/`](./Qatlib/Concepts/WalkSearch)<br>[`Qatlib/Papers/GroverSearch96/`](./Qatlib/Papers/GroverSearch96)<br>[`Qatlib/Papers/SpanProgram07/`](./Qatlib/Papers/SpanProgram07) |
| **4. Algebraic, Number-Theoretic & Cryptanalytic Quantum Algorithms** | QFT and Fourier sampling, Shor's factoring and discrete-log period recovery, elliptic-curve discrete logarithm (ECDLP) resource estimates, abelian and non-abelian hidden subgroup problems (HSP), Simon decoding and symmetric cryptanalysis, conditional lattice reductions | [`Qatlib/Concepts/PeriodSampling/`](./Qatlib/Concepts/PeriodSampling)<br>[`Qatlib/Concepts/CurveGroups/`](./Qatlib/Concepts/CurveGroups)<br>[`Qatlib/Concepts/HspRecovery/`](./Qatlib/Concepts/HspRecovery)<br>[`Qatlib/Concepts/AbelianDecoders/`](./Qatlib/Concepts/AbelianDecoders)<br>[`Qatlib/Papers/ECDLPResource17/`](./Qatlib/Papers/ECDLPResource17)<br>[`Qatlib/Papers/DihedralHSP04/`](./Qatlib/Papers/DihedralHSP04) |
| **5. Quantum Linear Algebra, Block-Encoding & QSVT / QSP** | Block-encoding algebra, quantum signal processing (QSP), quantum singular value transformation (QSVT), qubitization, linear combination of unitaries (LCU), HHL and quantum linear systems, and matrix function approximation | [`Qatlib/Concepts/BlockEncoding/`](./Qatlib/Concepts/BlockEncoding)<br>[`Qatlib/Concepts/QsvtCore/`](./Qatlib/Concepts/QsvtCore)<br>[`Qatlib/Concepts/QsvtLinearSolve/`](./Qatlib/Concepts/QsvtLinearSolve)<br>[`Qatlib/Concepts/HhlAlgorithms/`](./Qatlib/Concepts/HhlAlgorithms)<br>[`Qatlib/Concepts/SignalPrimitive/`](./Qatlib/Concepts/SignalPrimitive)<br>[`Qatlib/Papers/QSingValue19/`](./Qatlib/Papers/QSingValue19) |
| **6. Hamiltonian Simulation, Open Systems & Scientific Computing** | Lie–Trotter–Suzuki product formulas and commutator error bounds, truncated Taylor series, QSP Hamiltonian simulation, LCHS linear differential equation simulation, qDRIFT randomized Hamiltonian simulation, Lindblad evolution, quantum Gibbs sampling, and Monte Carlo estimation | [`Qatlib/Concepts/TrotterFormula/`](./Qatlib/Concepts/TrotterFormula)<br>[`Qatlib/Concepts/QspSimulation/`](./Qatlib/Concepts/QspSimulation)<br>[`Qatlib/Concepts/LchsSimulation/`](./Qatlib/Concepts/LchsSimulation)<br>[`Qatlib/Concepts/LindbladFlow/`](./Qatlib/Concepts/LindbladFlow)<br>[`Qatlib/Concepts/QuantumGibbs/`](./Qatlib/Concepts/QuantumGibbs)<br>[`Qatlib/Papers/TrotterError19/`](./Qatlib/Papers/TrotterError19) |
| **7. Many-Body Physics, Quantum Chemistry & Tensor Networks** | Jordan–Wigner and Bravyi–Kitaev fermionic mappings, bosonic Fock spaces, quantum chemistry simulation, and tensor networks | [`Qatlib/Concepts/FermionAlgebra/`](./Qatlib/Concepts/FermionAlgebra)<br>[`Qatlib/Concepts/BosonFock/`](./Qatlib/Concepts/BosonFock)<br>[`Qatlib/Concepts/TensorNetwork/`](./Qatlib/Concepts/TensorNetwork)<br>[`Qatlib/Papers/BKFermion17/`](./Qatlib/Papers/BKFermion17)<br>[`Qatlib/Papers/QChemistry14/`](./Qatlib/Papers/QChemistry14) |
| **8. Quantum Optimization, Quantum Machine Learning & Complexity** | Adiabatic quantum computation and spectral gap bounds, QAOA and the Overlap Gap Property, quantum semidefinite programming (SDP) solvers, local Hamiltonians and QMA completeness, quantum PCA, and variational circuit trainability | [`Qatlib/Concepts/SdpDuality/`](./Qatlib/Concepts/SdpDuality)<br>[`Qatlib/Concepts/SdpMmwSolver/`](./Qatlib/Concepts/SdpMmwSolver)<br>[`Qatlib/Concepts/QmaCompleteness/`](./Qatlib/Concepts/QmaCompleteness)<br>[`Qatlib/Papers/SDPBrandao16/`](./Qatlib/Papers/SDPBrandao16)<br>[`Qatlib/Papers/QAOAScaling23/`](./Qatlib/Papers/QAOAScaling23)<br>[`Qatlib/Papers/Trainability23/`](./Qatlib/Papers/Trainability23) |
| **9. Quantum Error Correction (QEC)** | Stabilizer and CSS code constructions, coherent recovery, code parameter certificates, syndrome extraction circuits, and decoding | [`Qatlib/Concepts/ErrorCorrection/`](./Qatlib/Concepts/ErrorCorrection)<br>[`Qatlib/Concepts/CodeCert/`](./Qatlib/Concepts/CodeCert)<br>[`Qatlib/Concepts/CodingDecoding/`](./Qatlib/Concepts/CodingDecoding)<br>[`Qatlib/Concepts/CssGreedyDecode/`](./Qatlib/Concepts/CssGreedyDecode) |

See [`docs/architecture.en.md`](./docs/architecture.en.md) for a detailed module overview.

## <a id="quantum-error-correction"></a>Quantum Error Correction Guide

### Stabilizer Algebra and Code Construction

Phased Pauli operators and signed Clifford tableaux formalize the semantics of stabilizer projections and measurements, while binary linear-code interfaces connect generator spaces and parity-check matrices to Calderbank–Shor–Steane (CSS) code constructions. [Stabilizer algebra](./Qatlib/Concepts/PauliClifford/PauliAlgebra/CliffordStabilizer.lean) · [Classical linear codes](./Qatlib/Concepts/ErrorCorrection/CssBuild/Classical.lean) · [CSS construction](./Qatlib/Concepts/ErrorCorrection/CssBuild/Constructions.lean)

Concrete developments cover classical repetition and Hamming codes, the Steane `[[7,1,3]]` code, and the non-CSS five-qubit `[[5,1,3]]` perfect code; under an explicit pairing condition, the generic Armillary permutation-block construction establishes upper bounds on check ranks together with lower bounds on the number of logical qubits and on the code rate. [Repetition codes](./Qatlib/Papers/CssCodeCS96/Construction/Repetition.lean) · [Hamming codes](./Qatlib/Papers/CssCodeCS96/Construction/Hamming.lean) · [Steane code](./Qatlib/Papers/CssCodeCS96/Construction/Steane.lean) · [Five-qubit code](./Qatlib/Papers/PerfectQEC96/FiveQubit.lean) · [Armillary parameter bounds](./Qatlib/Papers/Armillary26/Instances/Construction.lean)

### Coherent Error Recovery

Given an isometric encoding and complete noise and recovery Kraus families, recovery preserves encoded states—including mixed states and entanglement with any finite-dimensional reference system—whenever every noise Kraus operator lies in the recovery's correctable subspace. Transporting the same CSS decoder into the signed-tableau representation yields equivalent recovery channels on every input operator. [Kraus recovery with a finite reference](./Qatlib/Concepts/ErrorCorrection/Recovery/Kraus.lean) · [CSS and tableau channel equivalence](./Qatlib/Concepts/ErrorCorrection/Recovery/CssChannel.lean)

### Code Parameter Certificates

Kernel-checked certificates verify exact `GF(2)` ranks computed by binary Gaussian elimination as well as the resulting CSS logical dimension `k` determined by the two check ranks. Branch-and-bound certificates verify CSS distance lower bounds—certifying the exact distance when paired with an attaining logical Pauli witness—while rectangle exclusion on the parity-check matrix rules out 4-cycles in the Tanner graph and an explicit 6-cycle witness certifies exact girth 6. Permutation-block modules provide block row elimination and rank upper bounds. [Rank and CSS dimension](./Qatlib/Concepts/CodeCert/RankCert/Binary.lean) · [Distance certificates](./Qatlib/Concepts/CodeCert/DistCert/Branch.lean) · [Tanner girth](./Qatlib/Concepts/CodeCert/DistCert/Tanner.lean) · [Permutation-block rank](./Qatlib/Concepts/CodeCert/PermBlocks/Rank.lean)

### Syndrome Extraction and Decoding

Ordered CNOTs and qubitwise Hadamards realize the CSS syndrome-extraction instrument whenever the two gate sequences implement the `X` and `Z` parity-check matrices. Under a gate-indexed bit-flip model tracking readout shifts and residual data errors, if each fault flips at most one data bit, the combined residual Pauli weight across the two rounds is at most the number of faulty gates. [CSS syndrome extraction circuit](./Qatlib/Concepts/CodingDecoding/CssRecovery/CssCircuit.lean) · [CNOT fault propagation](./Qatlib/Concepts/CodingDecoding/CssRecovery/ParityCircuit.lean)

Decoding components include executable CSS greedy bit-flipping, interfaces for quantum locally testable code (qLTC) families under uniform parameter assumptions, and decoder specifications for quantum Tanner and lifted-product codes. A noisy-syndrome interface specifies single-shot correctness within prescribed data and measurement error budgets, complemented by selected residual bounds in quantum LDPC paper modules. [CSS greedy decoding](./Qatlib/Concepts/CssGreedyDecode/SyndromeGreedy/QuantumLDPCDecoding.lean) · [qLTC families](./Qatlib/Concepts/CodingDecoding/FamilyAssembly/AsymptoticallyGoodQLTCFamily.lean) · [Quantum Tanner and lifted-product decoding](./Qatlib/Papers/QCodeDecoding22/MainResults/DecoderModel.lean) · [Noisy-syndrome decoding interface](./Qatlib/Concepts/CodingDecoding/CssTesters/CodingDecodingCoreDefs.lean) · [Single-shot LDPC residual bounds](./Qatlib/Papers/OneShotLDPC23/MainResults/ResidualBound.lean)

### Surface-Code Resource Estimates

Surface-code coverage in Qatlib is scoped to resource estimates under specified parameters, spanning RSA factoring and quantum chemistry simulation. [RSA factoring costs](./Qatlib/Papers/RSAFactoring19/MainResults/ResourceEstimate/SurfaceCodeCost.lean) · [Quantum chemistry simulation estimates](./Qatlib/Papers/TensorHyper20/MainResults/SurfaceCodeEstimate.lean)

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
