/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Mathlib.Algebra.Order.Floor.Semiring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

def sourceFold (P : ℕ) (z : Fin P) : ℕ := min z.val (P-z.val)

def foldedEstimate (P : ℕ) (z : Fin P) : ℝ :=
  (Real.sin (Real.pi*(sourceFold P z : ℝ)/(P : ℝ)))^2

theorem sourceFold_range (P : ℕ) (z : Fin P) : sourceFold P z ≤ P/2 := by
  dsimp [sourceFold]
  omega

theorem foldedEstimate_eq (P : ℕ) (z : Fin P) : foldedEstimate P z = aeEstimate P z := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le z.val) z.isLt)
  unfold foldedEstimate sourceFold aeEstimate
  by_cases hz : z.val ≤ P-z.val
  · rw [min_eq_left hz]
  · rw [min_eq_right (le_of_not_ge hz),Nat.cast_sub (Nat.le_of_lt z.isLt)]
    have he : Real.pi*((P : ℝ)-(z.val : ℝ))/(P : ℝ) =
        Real.pi-Real.pi*(z.val : ℝ)/(P : ℝ) := by
      field_simp
    rw [he,Real.sin_pi_sub]

def roundedCount (N P : ℕ) (z : Fin P) : ℕ :=
  ⌊(N : ℝ)*foldedEstimate P z+1/2⌋₊

theorem rounding_exact_of_half_window (x : ℝ) (t : ℕ) (hx : 0 ≤ x)
    (h : |x-(t : ℝ)| < 1/2) : ⌊x+1/2⌋₊ = t := by
  apply (Nat.floor_eq_iff (by linarith : 0 ≤ x+1/2)).mpr
  have he := abs_lt.mp h
  constructor <;> linarith [he.1,he.2]

theorem folded_count_nonneg (N P : ℕ) (z : Fin P) : 0 ≤ (N : ℝ)*foldedEstimate P z := by
  unfold foldedEstimate
  positivity

theorem roundedCount_exact (N P t : ℕ) (z : Fin P)
    (h : |(N : ℝ)*aeEstimate P z-(t : ℝ)| < 1/2) : roundedCount N P z = t := by
  unfold roundedCount
  apply rounding_exact_of_half_window _ t (folded_count_nonneg N P z)
  simpa only [foldedEstimate_eq] using h

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
