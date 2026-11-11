/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Randomized non-adaptive Pauli mixedness testing (Theorem 1.1)

Paper: arXiv:2608.18839v3, Theorem 1.1 (page 2 of the PDF):

> Mixedness testing can be performed with `n = Õ(√(10^N)/ε²)` copies using
> non-adaptive, randomized Pauli basis measurements.

The theorem is formalized against the paper-local protocol model of
`Model/SourceModel.lean`: a `PauliBasisProtocol N n Ω` fixes, for every seed
`ω ∈ Fin Ω`, a list of `n` Pauli bases (non-adaptive), and a decision rule on
the `n` outcome registers; its acceptance mass is the uniform average over the
seed of the product Born outcome laws.  `IsPauliMixednessTester T ε` is the
paper's correctness requirement (accept `ρ_mm` with probability at least `2/3`,
reject every state at trace distance at least `ε` with probability at least
`2/3`).

The `Õ` hides a polynomial factor in `N`; the statement therefore existentially
quantifies an explicit polynomial loss `(N+1)^j` and a constant `C > 0`.

## Proof status (scaffolds removed; statements in branch history c93d182c6)

* Fixed source: arXiv:2608.18839v3, Theorem 1.1, §4.2 (algorithm) and
  Appendix A (analysis).
* Key proof route: (i) Paula decomposition `ρ = Σ_Q α_Q Q`; (ii) for a uniformly
  sampled Pauli basis `P`, the Pauli influence `L_P` has expectation `L = Σ α_Q²`
  (Lemma 2.2 / Appendix A.1); (iii) Levin's work-investment strategy allocates
  `Õ(3^i)` copies to the levels `L_P ≥ 3^{i-2} L`; (iv) inside one level, the
  outcome distribution is `(Δ,k,β)`-wise correlated and `KrawtChk`
  (Theorem 2.4) tests it with `Õ(√(C(N,k))/(βΔ))` samples; (v) summing over
  levels gives `Õ(√(10^N)/ε²)` because `Σ_w 9^w C(N,w) = 10^N`.
* Lean gap: the statement quantifies over the paper-local protocol class, but the
  construction of the tester (the concrete basis schedule and `KrawtChk`-based
  decision rule) and the multi-level sampling analysis are not formalized.  The
  analytic core would need: the fiber-counting identity for `E[L_P] = L`
  (see `Influence/Detectability.lean`), the `KrawtChk` correctness bridge
  (`Krawtchouk/TesterCorrectness.lean`), and a union bound over levels.
* Reusable dependencies: `SourceModel.pauliProtocolAcceptMass`,
  `IsPauliMixednessTester`, frozen `tensorPauliLaw`, `krawtchouk_tester_correct`,
  `FinDist.expect`/`union_bound` from `MonteCarloMean.FinDistBounds`.
* Suggested tactics: build the protocol by `Classical.choose` from the paper's
  parameters, then `nlinarith`/`positivity` for the copy-count arithmetic, and
  `Finset.sum_le_sum` + Chernoff/Chebyshev (`FinDist.chebyshev`) for the
  per-level error.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.RandomizedTester

open Qatlib.Foundations.PureStateMath


end Qatlib.Papers.MixednessTest26.MainResults.RandomizedTester
