# Library Architecture & Module Design

> 🌐 [中文版](./architecture.md)

## 1. Layered Dependency Structure

The `Qatlib` module tree under [`Qatlib/`](../Qatlib) is organized bottom-up into three layers with strictly one-way dependencies (`Foundations ← Concepts ← Papers`, enforced by `lake lint`):

1. **[`Qatlib/Foundations/`](../Qatlib/Foundations) (Shared Mathematical Structures & Base Semantics)**
   Provides foundational mathematical infrastructure with no dependencies on `Concepts` or `Papers`:
   - Matrix analysis and operator norms (operator norm, trace norm, Schatten norms, positive semidefinite order, and mixed-state fidelity);
   - Probability and concentration inequalities, graph structures and Laplacians, primality and group order foundations;
   - Finite-precision arithmetic, bit-word codecs, numerical error propagation, and time-evolution propagators.

2. **[`Qatlib/Concepts/`](../Qatlib/Concepts) (Reusable Domain Theories, Algorithmic Frameworks & Complexity Interfaces)**
   Built on `Foundations`, this layer captures reusable domain theories, algorithmic primitives, lower-bound frameworks, and execution accounting (including generalizable frameworks extracted from individual papers):
   - Quantum channels (CPTP, Stinespring, Choi–Kraus), quantum entropy, entanglement, instruments, hybrid quantum-classical execution (`Execution`), and resource accounting (`ResourceBounds`);
   - Block-encoding algebra (`BlockEncoding`), quantum signal processing (`QspSimulation`, `SignalPrimitive`), and quantum singular value transformation (`QsvtCore`, `QsvtLinearSolve`, `HhlAlgorithms`);
   - Linear combination of unitaries (LCU), amplitude amplification and estimation (`AmplitudeCore`, `AmplitudeSearch`), period sampling and HSP recovery (`PeriodSampling`, `HspRecovery`, `AbelianDecoders`);
   - Quantum walk frameworks (`WalkSearch`), polynomial degree method (`QueryComplexity`), and adversary lower bounds (`AdversaryBounds`);
   - Fermionic mappings (`FermionAlgebra`), bosonic Fock spaces (`BosonFock`), tensor networks (`TensorNetwork`), error-correction decoders (`CodingDecoding`), and SDP duality/solvers (`SdpDuality`, `SdpMmwSolver`).

3. **[`Qatlib/Papers/`](../Qatlib/Papers) (Paper-Specific Formalizations & Resource Analyses)**
   Built on `Foundations` and `Concepts`, each directory (`<TopicOrAuthor><YY>`, such as `GroverSearch96`, `SolovayKitaev05`, `QSingValue19`, `ClassShadows20`, `ECDLPResource17`) formalizes selected model definitions, technical lemmas, main theorems (typically under `MainResults/`), and end-to-end resource bounds from a specific paper.

## 2. Module Layout & Naming Conventions

To keep namespaces predictable and minimize compilation fan-out across thousands of files, `Qatlib` follows these conventions:

- **Strict `UpperCamelCase` module paths**: Every directory and `.lean` file stem uses `UpperCamelCase` (e.g., `Qatlib/Concepts/QsvtCore/`, `Qatlib/Papers/GroverSearch96/`).
- **Topic-focused splitting of definitions and proofs**: In multi-file directories, core data structures and model definitions live in `Defs.lean`, `*Defs.lean`, or `Basic.lean`, technical lemmas are split into focused topic files, and paper endpoint theorems are grouped under `MainResults/`.
- **Targeted leaf imports**: `Qatlib.Foundations`, `Qatlib.Concepts`, and `Qatlib.Papers` serve as directory/namespace prefixes; modules should import the specific leaf modules they need (e.g., `import Qatlib.Papers.GroverSearch96.MainResults.GainConvergence`) rather than the top-level `Qatlib` umbrella module.
