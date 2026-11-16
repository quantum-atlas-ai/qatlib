/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

@[expose] public section


/-! # A finite first-hit distribution identity (arXiv:1705.01843v4 Lemma 47).
The sampling process and its oracle cost are separate obligations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QSDPsolver17.MainResults

/-- Total probability mass of the values `≤ x_k`: `Pr(X ≤ x_k)`. -/
def prefixMass {N : ℕ} (p : Fin N → ℝ) (k : Fin N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), p i

/-- Probability that the first sampled index in `{0, …, k}` equals `i`
(extended by `0` outside `{0, …, k}`). -/
def firstHitProb {N : ℕ} (p : Fin N → ℝ) (k : Fin N) (i : Fin N) : ℝ :=
  if i ≤ k then p i / prefixMass p k else 0

/-- **Lemma 47** (arXiv:1705.01843v4, p. 32).  Let `X` be a finite discrete
random variable with values `x_1 < … < x_N`, and let `S(X)` be the random set
of values sampled during a run of Meta-Algorithm 2 on input `X`.  If
`k ∈ [N]`, then `Pr(x_k ∈ S(X)) = Pr(X = x_k) / Pr(X ≤ x_k)`.

Lean form: the first-hit distribution of the sampling process assigns to
`x_k` the probability `p_k / prefixMass p k`, and its total mass is `1`. -/
theorem lemma47_first_hit {N : ℕ} (p : Fin N → ℝ) (k : Fin N)
    (hk : prefixMass p k ≠ 0) :
    firstHitProb p k k = p k / prefixMass p k ∧
      (∑ i, firstHitProb p k i) = 1 := by
  constructor
  · simp [firstHitProb]
  · have hsum : (∑ i, firstHitProb p k i) =
        ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), p i / prefixMass p k := by
      rw [Finset.sum_filter]
      simp [firstHitProb]
    rw [hsum, ← Finset.sum_div]
    exact div_self hk


end Qatlib.Papers.QSDPsolver17.MainResults
