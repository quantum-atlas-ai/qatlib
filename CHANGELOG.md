# Changelog

All notable changes to **Qatlib** are documented in this file.

## Versioning Policy

* **Toolchain baseline tags (`v4.X.0`)**: Immutable tags pinned 1:1 to the initial
  verified snapshot for the Lean / Mathlib / Physlib `v4.X.0` toolchain.
* **Rolling releases (`main`)**: Every commit published on `main` is a complete,
  self-contained public release dated in UTC (with `.2`, `.3`, … suffixes when
  multiple releases land on the same UTC date), accompanied by precompiled Lake
  caches (`qatlib-env run -- lake update Qatlib` followed by
  `qatlib-env run -- lake exe get_cache`).

---

## [2026-11-20] — Quantum Error Correction, Rational Pilot Arithmetic, Span Programs, and Semantic Interfaces

### Added

* **Concepts — Quantum error-correction certificates, Kraus recovery, and syndrome circuits**:
  Certify exact `GF(2)` parity-check ranks and CSS logical dimensions `k` via
  kernel-checked Gaussian-elimination witnesses. Provide branch-and-bound
  soundness certificates for CSS distance lower bounds together with
  parity-check-to-Tanner bipartite graph bridges certifying four-cycle exclusion
  and exact girth six. Establish coherent Kraus error recovery over certified
  correctable subspaces—covering mixed states and entanglement with arbitrary
  finite reference systems—and prove channel equivalence between CSS and
  signed-tableau decoders. Formalize ordered-CNOT and bitwise-Hadamard CSS
  syndrome-extraction instruments, gate-indexed bit-flip fault propagation,
  residual weight bounds, and single-shot noisy-syndrome decoding contracts.
* **Concepts — Executed rational pilot moments**: Evaluate the exact empirical
  mean, second moment, and record count of a supplied rational table via binary
  arithmetic that tracks its own Boolean-gate charge. Bound this arithmetic gate
  charge on supplied samples by `3565 * (encodedSize + 1)^4`, and bound the
  output-register width of each rational result by twice the encoded size.
* **Papers — Classical shadows and positive-input span programs**: Verify that
  the binary arithmetic evaluator agrees with the rational pilot moments used in
  classical shadows while charging at least one arithmetic gate per supplied
  record. Construct a literal-supported span-program composition from an outer
  program and explicit inner programs for both Boolean outcomes; for accepting
  inputs with finite input costs, prove two positive witness-size bounds in the
  paired-program model and certify the one-bit identity example.
* **Public interface checks**: Exercise the renamed declarations and new quantum
  error-correction interfaces from ordinary Lean modules—covering Steane and
  non-CSS five-qubit recovery, rank, distance, and girth certificates, and
  syndrome-circuit fault-propagation instances—alongside signed and empty inputs
  for the rational moment evaluator and acceptance and rejection checks for the
  one-bit span-program composition.
* **Bibliography**: Add the cited revision of Shelby Kimmel's *Quantum
  Adversary (Upper) Bound*.

### Changed

* **Semantic declaration names**: Rename 378 declarations across the library to
  reflect their mathematical content, and update imports of the matrix
  optimization evidence module to
  `Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationContractEvidence`.
* **Mathematical documentation**: Rewrite 3,717 generic docstrings to state the
  concrete objects, hypotheses, and guarantees across finite constructions,
  gauge and polynomial interfaces, spinor sampling, matrix words, and rational
  quantum signal processing.

### Fixed

* **Theorem documentation and cross-references**: Supply missing docstrings for
  three public theorems and repair 65 stale declaration references.

---

## [2026-11-18] — Quantum Codes, Circuit Semantics, and Fluid and Optical Models

### Added

* **Foundations — Scaled rational square roots**: Certify natural-scale integer
  square-root floors for nonnegative rational inputs, including zero inputs and
  zero scale, proving fixed-scale monotonicity of the unsigned count and an
  absolute approximation error strictly less than `1` under either sign.
* **Concepts — Error correction and code certificates**: Construct CSS codes
  from classical parity-check matrices and connect syndrome quotient classes,
  logical distance bounds, and certified decoder recovery through shared
  interfaces. Provide signed stabilizer recovery contracts, CSS-to-Pauli
  operator and weight bridges, and permutation-block algebra with reusable rank
  certificates.
* **Concepts — Circuit semantics and resource models**: Establish compositional
  semantics for wire relabelings, local and controlled gates, standard XOR
  oracles, and finite measurement programs, and link compiled
  multi-controlled-NOT networks to their exact matrix denotations and gate
  counts. Track elementary gates, macro gates, oracle queries, and literal
  `T`/`T`-adjoint occurrences in distinct resource units with compositional
  budgeting and query-billing laws.
* **Papers — Quantum error correction**: Link the binary Hamming construction
  in fixed column order to the seven-qubit Steane code and certify its exact
  distance of three, alongside repetition-code and source-coordinate
  constructions. Provide a signed stabilizer presentation of the perfect
  five-qubit code, certifying exact distance three and pure-state recovery for
  every signed single-qubit Pauli error. For the twelve-group routed Armillary
  construction under the channel, shift, and visit-order pairing hypotheses,
  prove static check compatibility, cancellation of the time-ordered check sum,
  at least `6P + 4` encoded qubits for `P` data coordinates per group, and an
  encoding rate strictly above `1/2`.
* **Papers — Query algorithms, oracles, and amplitude amplification**: Connect
  quantum Fourier sampling in Simon's problem to independent uniform draws from
  the hidden subgroup's character annihilator; when the annihilator has known
  size `N >= 2`, bound the expected query count of the rank-stopping procedure
  by `2 log_2 N` and establish exact subgroup recovery on supported sample
  records, alongside conditional single-pass query reductions. Add
  uniform-sampling subgroup-generation bounds, adaptive decision-tree recovery,
  variable-time amplitude amplification cost and coherent-stopping assemblies,
  and a zero-outcome Fourier readout identity. Establish finite joint-coupling
  expected-distance bounds for random permutation oracles, a concrete two-bit
  Deutsch–Jozsa oracle comparison, a two-qubit QFT gate count, and
  additive-oracle resource accounting.
* **Papers — Hamiltonian simulation and linear-system cost models**: Construct
  truncated-Taylor `PREPARE` and `SELECT` circuit words on binary registers with
  identity extension on the encoding complement, factorial-weight preparation
  amplitudes, series remainder bounds, and multi-segment resource and
  conditional operator-error composition bounds. Develop Suzuki multi-product
  operator words, derive approximation-order improvements from moment
  cancellation, and prove quantitative Taylor-defect and state-normalized
  correction bounds under explicit operator-approximation hypotheses, together
  with an unconditional state-normalized algebraic composition identity across
  vanishing intermediate denominators. Add Trotter and Suzuki defect bounds,
  lattice counterexamples identifying hypotheses required in Trotter error
  estimates, and scalar preconditioned and finite-element cost comparisons under
  explicit spectral and scaling assumptions.
* **Papers — Quantum information and sampling interfaces**: Extend
  finite-dimensional state and channel theory with Kraus representations,
  quantum entropy inequalities, fidelity bounds, and conditional capacity,
  protocol, and recovery interfaces, and derive conditional generative-sampling
  implications from explicit sampler and hardness interfaces.
* **Papers — Fluid, optical, and hydrodynamic spin models**: Formalize phase
  winding, circulation quantization, and discrete Kutta–Joukowski lift
  increments in an idealized point-vortex superfluid model under closed
  phase-lift and regularity hypotheses, together with local polar Madelung
  currents, relabeling-charge cancellation, Clebsch curl and helicity-divergence
  identities, and finite vortex-line linking decompositions. Establish complex
  bilinear null-field characterizations, inverse stereographic and Hopf
  unit-sphere identities, quaternion tangent frames on the three-sphere, and
  scalar helicity conservation under integrated balance and duality hypotheses;
  prove Bateman null-field constructions under explicit compatibility conditions
  (paired with non-null counterexamples when compatibility is omitted),
  two-potential reparametrization determinant laws, rational three-sphere
  identities, weighted-homogeneous torus-knot polynomial identities, and
  finite-mode quadratic charge conservation. In idealized finite-dimensional
  hydrodynamic spin models, prove single-spin Rayleigh drift reductions,
  quartic-potential global minimizers, finite ferromagnetic and bipartite
  antiferromagnetic Ising ground-state criteria (contrasting even-cycle
  alternating order with odd-cycle frustration), and network energy dissipation
  under first-order symmetrically coupled gradient dynamics. In an
  auxiliary-coordinate Navier–Stokes linearization model, prove linear readout
  of a cubic term with a time derivative and finite-step termination by strictly
  decreasing total order.
* **Public interface regression suite**: Add 32 strict consumer and
  public-interface test modules, including ordinary `module` consumers and
  executable computability probes, compiled with warnings treated as errors
  ahead of the full kernel axiom audit.
* **Release-history portal and responsive navigation**: Add English and Chinese
  release-history portal pages linked from the home page, header, footer, and
  sidebar navigation, keeping search controls, narrow-screen menus, and keyboard
  focus accessible across desktop and mobile layouts.

### Changed

* **Mathematical naming and source bibliography**: Standardize declaration
  names to reflect their mathematical hypotheses and conclusions, synchronize
  inline source citations across the new developments, and expand the
  bibliography by 10 entries.
* **Documentation site typography**: Adopt modern sans-serif and monospace font
  stacks with language-aware spacing, heading weights, and form-control font
  inheritance across the documentation portal and API pages.
* **Documentation build pipeline**: Support credential-free documentation
  builds with compatible artifact reuse and strict incremental fallback
  compilation when needed, while normalizing canonical source links and
  validating complete HTML output across both read-only and publishing builds.

### Fixed

* **Bibliography citation links**: Align paper-index bibliography links with
  `#ref_` target anchors across the English and Chinese documentation portal
  pages.
* **Continuous integration checks**: Report a completed required build status
  for documentation-only pull requests via input-aware job selection while
  retaining full compilation and kernel axiom auditing for Lean changes, and
  cover documentation-pipeline and typography regressions in lint checks.

## [2026-11-16] — PPT Maps, Quantum State Fidelity, and Gibbs Operators

### Added

* **Library expansion**: Add 1,003 modules and 6,522 explicit public theorem and
  lemma declarations across finite algebra, probability, operator theory, and
  paper-linked mathematical developments.
* **PPT maps and entanglement breaking**: Prove that any ordered composition of at
  least `2(d-1)` PPT maps on complex `d`-by-`d` matrices is entanglement breaking
  for `d >= 2`, together with the corresponding index bound and an interleaving
  bound for a repeated PPT map with completely positive maps. Include Choi-matrix
  characterizations, separable block decompositions, and exact thin singular-value
  expansions.
* **Mixed-state fidelity and measurement**: Extend finite mixed-state interfaces
  with root-fidelity tensor-product and tensor-power identities, Fuchs–van de Graaf
  bounds, CPTP data processing, exact calibration of classical readout, and
  repeated-measurement laws, including zero-copy cases.
* **Gibbs parent operators and spectral gaps**: Develop full Bohr-transition Gibbs
  parent operators, unitary bridges between energy and physical coordinates,
  Gibbs-kernel descriptions, and attained gap eigenoperators. Establish strict
  spectral-gap positivity in dimension at least two (`d >= 2`) at positive inverse
  temperature under the stated scalar-common-commutant condition, with comparison
  estimates retaining their sparse-proposal or finite-certificate hypotheses,
  including the required population-energy bounds.
* **Analytic, algebraic, and discrete foundations**: Add complex-Gaussian moment
  integrals and controlled variance-rescaling bounds; fixed-particle bosonic
  occupation counts and homogeneous-polynomial bridges; explicit left-coset
  intersection and characteristic-`p` group-algebra identities; finite
  Cauchy-kernel positivity; and cost minima over positive integers certified by
  adjacent threshold inequalities.
* **Paper-linked mathematical developments**: Extend paper-linked formalizations
  across Hamiltonian simulation and signal processing; differential equations and
  linear algebra; query complexity and adversaries; graph search and quantum walks;
  finite-group and Fourier methods; number theory and cryptography; quantum
  information and error correction; bosonic and fermionic models; learning,
  statistics, optimization, and semidefinite programming; adiabatic computation and
  metrology; and homology and topological algorithms. Definitions, proved
  fragments, and conditional interfaces retain their stated mathematical scope.
* **Query, statistical, and circuit models**: Formalize finite-field learning
  executions with explicit oracle-query counts, finite Bernoulli
  likelihood-affinity bounds, balanced-qubit phase-preparation comparisons, and
  normalized output states and joint Born laws for modular-exponentiation
  order-finding circuits under the specified finite-carrier and circuit
  assumptions.
* **Worked examples, counterexamples, and stability bounds**: Provide genuine empty
  and nonempty coset-intersection examples alongside direct mixed-state consumers.
  Formalize a minimum-outcome-mass union bound paired with a counterexample to the
  maximum-mass variant, the forward-Euler obstruction to unrestricted A-stability,
  and vector-normalization error bounds retaining their explicit dependence on a
  nonzero target norm.

### Changed

* **Citation metadata and build cache**: Align project citation metadata with
  rolling releases and adopt Lake's default artifact-cache settings.
* **Library navigation and mathematical scope**: Refresh library navigation and
  clarify the provenance and mathematical scope of numerical-range,
  quaternion-field, spinor-preparation, and trine-state developments.

### Fixed

* **Documentation cross-references**: Update documentation cross-references to the
  current quantum-channel, time-evolution, query, and Fourier interfaces.
* **Toolchain compatibility**: Update deprecated Mathlib imports and proof
  interfaces for the pinned toolchain.
* **Rational QSP packet computability**: Provide a computable `Decidable` instance
  for the rational lexicographic endpoint order in the Sturm model and restore
  executable definitions for the rational QSP source-packet generation dispatchers.

---

## [2026-11-15] — Quantum Query, Operator, and Paper Formalizations

### Added

* **Library expansion**: 330 new modules and 3,471 public declarations across
  `Foundations` (11 modules), `Concepts` (245), and `Papers` (74), bringing the
  library to 10,390 modules.
* **Foundations**: Real and rational positive-semidefinite Gram factorizations,
  permanent perturbation and finite-product identities, normalized product
  complex-Gaussian translation bounds, phase-reconstruction stability, and
  projector and amplitude error estimates.
* **Quantum query models and bounds**: Resource-counted circuit and sampling
  interfaces, inverse-free amplitude-estimation bounds, graph-collision and
  cycle reductions, ordered-search SDP-to-circuit bridges, and polynomial-degree
  and spectral-sensitivity query bounds.
* **Polynomial, QSP, and operator constructions**: Laurent-polynomial completion
  and finite quantum signal-processing interfaces, corrected Fourier-grid
  accuracy and operation-count bounds (with formalized counterexamples
  delineating grid and functional-calculus threshold regimes), Cayley-transducer
  evolution approximations, and resource-counted block-encoding and
  Neumann/resolvent constructions.
* **Boolean analysis, quantum information, and CSS algebra**: Product-measure and
  Hamming-slice estimates for Boolean functions, variance/influence comparisons,
  distributional Aaronson–Ambainis equivalences, chain-complex CSS code algebra
  and conditional parameter bounds, finite-dimensional Lindblad mixing/gap
  estimates and two-level Gibbs-oracle lower bounds, linear-optical/Fock
  permanent identities, MQFI completion–separability bridges, and
  unextendibility and quantitative neighborhood stability certificates for the
  canonical dimension-six mutually unbiased basis triple.
* **Paper formalizations**: Exact inverse nonlinear Fourier reconstruction and
  uniqueness for normalized complementary SU(2) polynomial pairs with explicit
  operation-count bounds; linear lower bounds on the exact stabilizer rank of
  the `magicH` and `magicR` state families; finite-field triorthogonal CSS
  algebra together with local-stochastic union/entropy bounds and conditional
  threshold-based distillation overhead and error-decay estimates;
  query-preserving witness-circuit transport, compressed-database models, and
  conditional collision-task query bounds; and conditional cheat-sheet query
  bounds, forrelation range estimates, Krawtchouk polynomial bounds for
  mixedness testing, spatial quantum search guarantees under spectral-gap and
  overlap hypotheses, and commutator-based Trotter error accounting.

### Changed

* **API documentation**: Preserve bibliography outputs across incremental HTML
  regeneration and batch HTML staging cleanup on repeated documentation builds.

---

## [2026-11-14] — Lean 4.35 Module System and Verification Pipeline

### Changed

* **Lean 4.35 `module` system**: Migrated all 10,060 modules across
  `Foundations` (405 modules), `Concepts` (4,437), and `Papers` (5,218) to
  `module`, `public import`, and explicit `public section` export boundaries,
  with normalized module paths, two additional `Foundations/ProbabilityCore`
  modules, and updated root imports in `Qatlib.lean`.

### Added

* **Transitive verification**: Extended sorry-freeness and standard Lean axiom
  checks in `scripts/test.lean` to cover both public and private declarations
  transitively across the imported library.
* **Reproducible API documentation**: Added `docbuild/` configuration, cached
  HTML build scripts, and pipeline regression tests for reproducible API
  documentation generation and GitHub Pages deployment.

---

## [2026-11-13.3] — Third-Party Attribution, Statement Fidelity, and Interactive Explorers

### Added

* **Third-party attribution and governance**: Included Apache-2.0 `NOTICE` and
  upstream copyright and commit provenance headers for adapted `TauCeti` and
  `CausalSmith` (`Causalean`) components in `Foundations/CbmdAnalysis`, together
  with `CODE_OF_CONDUCT.md`, `SECURITY.md`, updated `CITATION.cff` metadata, and
  statement-fidelity reporting templates.
* **Interactive documentation explorers**: Upgraded `scripts/build_site.py` with
  searchable bilingual module, paper, and declaration explorers featuring
  per-layer summaries, inline declaration docstrings, direct source-line links,
  and statement-fidelity highlights.
* **Verification and lint gates**: Folded source-hygiene and `docs/references.bib`
  citation checks into `scripts/lint.lean`, enforced warning-clean (`--wfail`)
  source builds and prebuilt cache-manifest completeness checks, and added
  scheduled fresh kernel-replay verification.

### Changed

* **Mathematical statement fidelity**: Clarified hypotheses and result
  statements across paper formalizations including triangle finding
  (`TriangleFind14`), quantum linear systems (`QLSBeyondCond25`), dimension-six
  mutually unbiased bases (`MUBSixOpenAI26`), spectral gaps (`SpectralGap11`),
  and element distinctness (`ElemDistinct00`).
* **Namespace and instance scoping**: Scoped root-level declarations and Mathlib
  typeclass instances into `Qatlib` namespaces across 6,544 modules and restored
  qualified identifiers in complex-analysis developments.

---

## [2026-11-13.2] — Documentation Guide Heading Parsing

### Fixed

* **Guide rendering**: Ignore `#` comment lines inside fenced shell code blocks
  when extracting top-level Markdown headings in `scripts/build_site.py`,
  preserving the `Qatlib` page title across both English and Chinese `README`
  guides.

---

## [2026-11-13] — Paper Formalizations, Bilingual Portal, and Cross-Platform Cache

### Added

* **Paper formalizations**: Added 278 modules across 114 `Papers` directories
  (bringing `Qatlib` to 10,058 modules across `Foundations`, `Concepts`, and
  `Papers`), covering multivariate mean estimation, sublinear partition testing,
  circuit-depth bounds, quantum SDP solvers, Gevrey gradient methods, graph
  property testing, quantum dynamic programming, zero-sum game algorithms,
  block-encoded matrix powers, free-fermion dynamics, quantum regression, and
  universal quantum walks, with expanded `docs/references.bib` citations.
* **Bilingual documentation portal**: Added `scripts/build_site.py` and project
  wordmark assets to publish a unified English and Chinese documentation site
  alongside `doc-gen4` API reference pages.
* **Targeted kernel auditing**: Updated `scripts/test.lean` to support both
  full-library and targeted per-module kernel axiom audits via `lake --no-build lean`.

### Changed

* **Cross-platform Lake artifact cache**: Enabled native Lake v4.35
  platform-independent artifact caching (`enableArtifactCache = true`,
  `platformIndependent = true`) with repository-scoped manifest resolution in
  `scripts/get_cache.lean`.

---

## [2026-11-11.2] — Module Curation, Bibliography Standardization, and Docs Cache Verification

### Changed

* **Module curation and docstrings**: Refined the promoted `Papers` module
  selection (consolidating `Qatlib` at 9,780 verified modules across 403
  `Foundations`, 4,437 `Concepts`, and 4,940 `Papers` modules) and standardized
  module docstrings across 44 files.
* **Bibliography and documentation verification**: Completed missing literature
  entries in `docs/references.bib`, aligned `Qatlib.lean` root-import ordering
  checks in `scripts/lint.lean` with module-name sorting, and verified prebuilt
  Lake cache manifests before running `doc-gen4` in documentation builds.

---

## [2026-11-11] — Quantum Gauge, Matrix-Access, and Paper Formalizations

### Added

* **Library expansion**: Added 2,663 verified modules across `Foundations` (23
  modules), `Concepts` (718), and `Papers` (1,922 across 454 paper directories),
  expanding `Qatlib` from 7,267 to 9,930 modules.
* **Foundations and Concepts**: Added decision-risk bounds, finite-precision
  arithmetic, finite-sample statistics, matrix algebra, operator calculus, and
  probability concentration in `Foundations`; and effective gauge reductions,
  matrix-access and block-encoding backends, spinor sampling, copy-decision
  bounds, contour-integral operator representations, query complexity, Fourier
  recovery, mixed-state fidelity, Monte Carlo mean estimation, finite LOCC, and
  classical shadow models in `Concepts`.
* **Paper formalizations**: Expanded literature formalizations across ground-
  and superconducting-state preparation, Crouzeix linear-system bounds, causal
  hierarchies, certified randomness, shallow-circuit advantages and Lindbladian
  simulation, QAOA and spin-boson optimization, quantum LWE, truncated Taylor
  simulation, unambiguous measurement, and quantum interactive proofs.
* **Bibliography and build pipeline**: Added `docs/references.bib` (447 BibTeX
  entries) for API reference citation linking and introduced the `Build`
  verification workflow with precompiled Lake cache resolution and kernel axiom
  auditing.

---

## [`v4.35.0`] — Initial Lean v4.35.0 Baseline (2026-11-10)

* Initial open-source baseline of `Qatlib` on `leanprover/lean4:v4.35.0`,
  `mathlib4` (`v4.35.0`), and `Physlib` (`v4.35.0`), comprising 7,267 modules
  organized into `Foundations` (380 modules), `Concepts` (3,719), and `Papers`
  (3,168) with `lake exe get_cache`, `lake lint`, and `lake test` kernel axiom
  auditing.
