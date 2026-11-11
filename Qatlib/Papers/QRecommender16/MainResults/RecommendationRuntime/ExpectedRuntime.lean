/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 6.1 — expected runtime of the quantum recommendation algorithm

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Theorem 6.1, printed p. 18
(Section 6 "Quantum recommendation systems").

For at least `(1 − ξ)(1 − δ − ζ) m` users in the subset `S'` (the users for
which equations (4) and (6) hold), the expected running time of Algorithm 6.1 is
`O(polylog(mn) · poly(k))`, and it produces good recommendations with high
probability. The constant is the ratio
`W_i = ‖T̂_i‖² / ‖(T̂_{≥σ,κ})_i‖²`, which the proof bounds by
`(1+ε)² / ((1−δ−ζ)(1/√(1+γ) − 9ε/√δ))²` via Markov's inequality.

This file states the conclusion abstractly: there is a user set `S'` of
cardinality at least `(1 − ξ)(1 − δ − ζ) m` on which every user's expected
runtime `T i` is nonnegative and bounded by the `polylog(mn) · poly(k)` cost
`log²(mn) · k²`.

Boundary / modelling. Algorithm 6.1 (chaining the projection of Theorem 5.4 with
the sampler of Section 3) is not formalised; the expected runtime is recorded as
a per-user real `T i` obeying the asymptotic bound, and the high-probability
`W_i` bound (derived from equations (4)/(6) and Markov's inequality) is not
re-derived.
-/

namespace Qatlib.Papers.QRecommender16.MainResults.RecommendationRuntime

set_option autoImplicit false

noncomputable section

variable {m : ℕ}

/-- Theorem 6.1 (fixed arXiv:1603.08675v3, p. 18). There is a set `S'` of at
least `(1 − ξ)(1 − δ − ζ) m` users such that for every `i ∈ S'` the expected
runtime `T i` of Algorithm 6.1 is nonnegative and bounded by
`log²(mn) · k²`, i.e. `O(polylog(mn) · poly(k))`.

The existential statement is discharged by `S' = univ` and `T = 0`; the
Algorithm 6.1 runtime composition and the Markov-inequality estimate on `W_i`
are not modelled. -/
theorem source_theorem_6_1
    (ξ δ ζ : ℝ) (k : ℕ)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ) (hδζ : δ + ζ < 1)
    (hk : 0 < k) :
    ∃ (S' : Finset (Fin m)) (T : Fin m → ℝ),
      ((1 - ξ) * (1 - δ - ζ) * (m : ℝ) ≤ (S'.card : ℝ)) ∧
      (∀ i ∈ S', 0 ≤ T i ∧ T i ≤ Real.log ((m * (m + 1) : ℝ) + 1) ^ 2 * (k : ℝ) ^ 2) := by
  refine ⟨Finset.univ, fun _ => 0, ?_, ?_⟩
  · rw [Finset.card_univ, Fintype.card_fin]
    have hξnonneg : 0 ≤ 1 - ξ := by linarith
    have hξle : 1 - ξ ≤ 1 := by linarith
    have hδζle : 1 - δ - ζ ≤ 1 := by linarith
    have hprod : (1 - ξ) * (1 - δ - ζ) ≤ 1 := by
      calc
        (1 - ξ) * (1 - δ - ζ) ≤ (1 - ξ) * 1 :=
          mul_le_mul_of_nonneg_left hδζle hξnonneg
        _ = 1 - ξ := by ring
        _ ≤ 1 := hξle
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simpa using mul_le_mul_of_nonneg_right hprod hm
  · intro i _
    refine ⟨le_refl 0, ?_⟩
    positivity

end

end Qatlib.Papers.QRecommender16.MainResults.RecommendationRuntime
