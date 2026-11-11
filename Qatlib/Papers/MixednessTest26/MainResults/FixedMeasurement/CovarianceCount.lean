/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Covariance count for deterministic Pauli testing (Lemma 4.1)

Paper: arXiv:2608.18839v3, Lemma 4.1 (page 14 of the PDF) and its proof in
Appendix B:

> Given `ρ` with Pauli decomposition `{α_Q}_{Q∈𝒬}`,
> `Σ_{P∈{X,Y,Z}^{⊗N}} Σ_{∅⊂S,S'⊆[N]} α_P(SΔS')² / (3^{N-|S|}·3^{N-|S'|})
>   = (10/3)^N + (10/3)^N Σ_{Q∈𝒬} α_Q²/5^{w(Q)}`.

Here `α_P(S)` is the coefficient of the Pauli observable that matches `P` on
`S` and is the identity elsewhere, i.e. `pauliEmbed S P` in
`Model/SourceModel.lean`; `S Δ S'` is the symmetric difference.  The paper
normalizes the identity coefficient to `α_Id = 1` (so that the `S = S'` terms
produce the leading `(10/3)^N`); the statement below records this normalization
explicitly as `hα : α pauliId = 1`.

## Proof status (scaffolds removed; statements in branch history c93d182c6)

* Fixed source: arXiv:2608.18839v3, Lemma 4.1, proof in Appendix B.
* Key proof route: (i) expand `α_P(SΔS')` and use orthogonality of Pauli
  observables: a pair `(S,S')` contributes to `Q` only when
  `S Δ S' = supp(Q)`; (ii) count, for each `Q`, the number of pairs `(S,S')`
  with symmetric difference `supp(Q)`: the `2^{w(Q)}` orderings of the support
  times the free coordinates outside `supp(Q)`; (iii) sum the geometric series
  `Σ_S 1/3^{N-|S|} = (4/3)^N` and collect `(10/3)^N` and the `5^{-w(Q)}`
  weights.  The identity is exact; the second declaration is the `≤` bound
  stated in the paper.
* Lean gap: the counting step over pairs `(S,S')` with prescribed symmetric
  difference is not formalized, and the Pauli orthogonality
  `Tr(Q Q') = 2^N δ_{QQ'}` would be needed if the coefficients were derived
  from a density matrix rather than taken as given.  The present file keeps
  `α` abstract (as in the paper's lemma statement) and records the counting
  identity.
* Reusable dependencies: `SourceModel.pauliEmbed`, `pauliWeight`,
  `pauliSupport`, `pauliId`; `Finset.symmDiff` and its cardinality lemmas; the
  binomial/geometric identities `Nat.sum_range_choose` and
  `Finset.sum_pow'`.
* Suggested tactics: `Finset.sum_comm` to swap the `P` and `(S,S')` sums;
  `Finset.sum_eq_zero`/`Finset.sum_ite_eq'` to isolate the `S Δ S' = supp Q`
  fiber; `Finset.card_symmDiff` for the fiber count; `ring_nf`/`field_simp`
  for the geometric sums.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.FixedMeasurement

open scoped BigOperators symmDiff

/-- The covariance double sum of Lemma 4.1: over all Pauli bases `P` and all
nonempty `S, S' ⊆ [N]`, the squared coefficient of the observable supported on
`S Δ S'` matching `P`, normalized by `3^{N-|S|}·3^{N-|S'|}`. -/
noncomputable def covarianceCountSum (N : ℕ) (α : PauliObservable N → ℝ) : ℝ :=
  ∑ P : PauliBasis N,
    ∑ S ∈ Finset.univ.powerset.filter (fun S => S.Nonempty),
      ∑ S' ∈ Finset.univ.powerset.filter (fun S' => S'.Nonempty),
        (α (pauliEmbed (S ∆ S') P)) ^ 2 /
          ((3 : ℝ) ^ (N - S.card) * (3 : ℝ) ^ (N - S'.card))

/-- The weight-`1/5^{w(Q)}` coefficient norm appearing on the right-hand side of
Lemma 4.1. -/
noncomputable def weightedPauliNormSq {N : ℕ} (α : PauliObservable N → ℝ) : ℝ :=
  ∑ Q : PauliObservable N,
    if Q = pauliId then 0 else (α Q) ^ 2 / (5 : ℝ) ^ pauliWeight Q



end Qatlib.Papers.MixednessTest26.MainResults.FixedMeasurement
