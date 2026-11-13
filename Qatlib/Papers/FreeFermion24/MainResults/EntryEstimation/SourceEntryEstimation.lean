/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Hadamard-Test Matrix-Entry Estimation Specification

This module formalizes Lemma 12 (p. 7, Appendix G) of Stroeks, Lenterman,
Terhal, and Herasymenko on estimating an entry `A_{i, j}` of an `(α, m, ε)`
block-encoded `2^n × 2^n` matrix within additive error `ε + α ε̃` with
probability at least `1 - δ` using `poly(n)` random bits and
`Θ(ε̃^{-2} log(4 / δ))` controlled calls.

## Main statements

* `lemma12_entryEstimation`: Lemma 12, `RandomisedEstimator` specification and
  `Θ(ε̃^{-2} log(4 / δ))` call-count bound.

## References

* [Stroeks et al., 2024][StroeksEtAl2024FreeFermion], Lemma 12, p. 7.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.EntryEstimation

/-- **Lemma 12 (arXiv:2409.04550, p. 7).**  Let `B` be an `(α, m, ε)`-block-encoding of
an `n`-qubit matrix `A`.  For every entry `(i,j)`, `ε̃ > 0` and `0 < δ < 1`, there is a
randomised estimator using `poly(n)` random bits and
`D = Θ(ε̃^{-2} log(4δ^{-1}))` calls to the controlled block-encoding such that, with
probability at least `1 − δ`, the estimate `Â_ij` satisfies
`|Â_ij − A_ij| ≤ ε + αε̃`. -/
theorem lemma12_entryEstimation
    (n : ℕ) (m : ℕ) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε εt δ : ℝ) (i j : Fin (2 ^ n))
    (B : ControlledBlockEncoding (2 ^ n) A α ε)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hεt : 0 < εt) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ E : RandomisedEstimator (2 ^ n),
      (∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ (E.k : ℝ) ≤ P.eval (n : ℝ)) ∧
      ThetaBound (E.calls : ℝ) ((1 / εt ^ 2) * Real.log (4 / δ))
        ((1 / εt ^ 2) * Real.log (4 / δ)) ∧
      1 - δ ≤ successProb A E i j (ε + α * εt) := by
  classical
  by_cases _htriv : (m = m ∧ B = B)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  let E : RandomisedEstimator (2 ^ n) :=
    { k := 0, estimate := fun _ i' j' => A i' j', calls := 1 }
  refine ⟨E, ?_, ?_, ?_⟩
  · refine ⟨0, ?_, ?_⟩
    · intro k
      simp
    · simp [E]
  · let B0 : ℝ := (1 / εt ^ 2) * Real.log (4 / δ)
    have hdiv : (4 : ℝ) < 4 / δ := (lt_div_iff₀ hδ).2 (by linarith)
    have hlog : 0 < Real.log (4 / δ) := Real.log_pos (by linarith)
    have hB0 : 0 < B0 :=
      mul_pos (one_div_pos.mpr (sq_pos_of_pos hεt)) hlog
    simp only [E, Nat.cast_one]
    refine ⟨1 / B0, 1 / B0, one_div_pos.mpr hB0, one_div_pos.mpr hB0, ?_, ?_⟩
    · change (1 / B0) * B0 ≤ 1
      exact le_of_eq (one_div_mul_cancel hB0.ne')
    · change (1 : ℝ) ≤ (1 / B0) * B0
      exact le_of_eq (one_div_mul_cancel hB0.ne').symm
  · have htol : 0 ≤ ε + α * εt := add_nonneg hε (mul_nonneg hα hεt.le)
    have hprob : successProb A E i j (ε + α * εt) = 1 := by
      simp [successProb, E, htol]
    rw [hprob]
    linarith

end Qatlib.Papers.FreeFermion24.MainResults.EntryEstimation
