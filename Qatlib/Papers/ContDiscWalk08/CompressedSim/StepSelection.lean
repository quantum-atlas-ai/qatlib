/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Selecting a simulation step parameter

The theorem `step_count_suffices` verifies a real-valued sufficient lower bound on the step
parameter for the error expression in equation (26) of [Childs2010]. It combines the accuracy
threshold with the normalization constraint.

## Main statements

* `step_count_suffices`: the prescribed lower bounds on `τ` imply error at most `δ`.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ContDiscWalk08.CompressedSim

/-- Under the stated positivity and normalization assumptions, the accuracy and normalization
lower bounds on `τ` make the simulation error expression at most `δ`. This verifies the
real-parameter inequality associated with equation (26) of [Childs2010]. -/
theorem step_count_suffices {Hnorm absH t δ τ : ℝ}
    (hH0 : 0 ≤ Hnorm) (hH : Hnorm ≤ absH) (habs : 0 < absH)
    (hδ : 0 < δ) (ht : 0 ≤ t)
    (hτ : Hnorm * t * Real.sqrt ((1 + (Real.pi / 2 - 1) * (Hnorm * t)) / δ) ≤ τ)
    (hτ' : absH * t ≤ τ) :
    (Hnorm * t) ^ 2 / τ ^ 2 * (1 + (Real.pi / 2 - 1) * (Hnorm * t)) ≤ δ := by
  set A := Hnorm * t with hAdef
  set K := Real.pi / 2 - 1 with hKdef
  have hK0 : 0 ≤ K := by
    have h := Real.pi_gt_three
    rw [hKdef]
    linarith
  have hA0 : 0 ≤ A := mul_nonneg hH0 ht
  have hAle : A ≤ τ := by
    rw [hAdef]
    exact le_trans (mul_le_mul_of_nonneg_right hH ht) hτ'
  by_cases hAzero : A = 0
  · rw [hAzero]
    norm_num
    exact hδ.le
  · have htpos : 0 < t := by
      rcases lt_or_eq_of_le ht with h | h
      · exact h
      · exfalso
        apply hAzero
        rw [hAdef, ← h]
        ring
    have hτpos : 0 < τ := lt_of_lt_of_le (mul_pos habs htpos) hτ'
    have hKA0 : 0 ≤ 1 + K * A := by nlinarith [hK0, hA0]
    set b := (1 + K * A) / δ with hbdef
    have hbpos : 0 < b := by
      rw [hbdef]
      positivity
    have hstep : A * Real.sqrt b ≤ τ := by
      rw [hAdef, hbdef] at hτ ⊢
      exact hτ
    have hsquare : A ^ 2 * b ≤ τ ^ 2 := by
      have hnn : 0 ≤ A * Real.sqrt b := mul_nonneg hA0 (Real.sqrt_nonneg _)
      have h := pow_le_pow_left₀ hnn hstep 2
      rw [mul_pow, Real.sq_sqrt (le_of_lt hbpos)] at h
      exact h
    have hb' : A ^ 2 * (1 + K * A) / δ ≤ τ ^ 2 := by
      rw [mul_div_assoc]
      simpa [hbdef] using hsquare
    have hb : A ^ 2 * (1 + K * A) ≤ δ * τ ^ 2 := by
      rw [div_le_iff₀ hδ] at hb'
      nlinarith [hb']
    calc A ^ 2 / τ ^ 2 * (1 + K * A)
        = A ^ 2 * (1 + K * A) / τ ^ 2 := by ring
      _ ≤ δ := by
          rw [div_le_iff₀ (pow_pos hτpos 2)]
          exact hb

end Qatlib.Papers.ContDiscWalk08.CompressedSim
