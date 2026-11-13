/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Folded phase estimates and exact rounding

This module defines the phase-label fold `sourceFold`, the squared-sine estimate
`foldedEstimate`, and the natural-number output `roundedCount` used in
[BrassardHoyerTapp1998Counting]. Folding a label to the nearer endpoint leaves the amplitude
estimate unchanged.

The rounding lemmas show that a nonnegative estimate within a strict half-unit window around a
natural number yields that number after adding one half and taking the natural floor.

## Main statements

* `sourceFold_range`: the folded label lies at most halfway around the phase grid.
* `foldedEstimate_eq`: folding preserves `aeEstimate`.
* `roundedCount_exact`: a strict half-unit count window gives the exact rounded count.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Qatlib.Concepts.AmplitudeCore.PreparedReadout

/-- The phase-label fold `min z.val (P - z.val)` on a grid of size `P`. -/
def sourceFold (P : ℕ) (z : Fin P) : ℕ := min z.val (P-z.val)

/-- The amplitude estimate `sin² (π * sourceFold P z / P)` obtained from the folded phase label. -/
def foldedEstimate (P : ℕ) (z : Fin P) : ℝ :=
  (Real.sin (Real.pi*(sourceFold P z : ℝ)/(P : ℝ)))^2

/-- The folded phase label is at most the natural-number quotient `P / 2`. -/
theorem sourceFold_range (P : ℕ) (z : Fin P) : sourceFold P z ≤ P/2 := by
  dsimp [sourceFold]
  omega

/-- Folding the phase label leaves the amplitude estimate `aeEstimate P z` unchanged. -/
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

/-- The natural-number count obtained by taking the floor of `N * foldedEstimate P z + 1 / 2`. -/
def roundedCount (N P : ℕ) (z : Fin P) : ℕ :=
  ⌊(N : ℝ)*foldedEstimate P z+1/2⌋₊

/-- A nonnegative real number at distance strictly less than one half from a natural number `t`
rounds to `t` under the natural floor of `x + 1 / 2`. -/
theorem rounding_exact_of_half_window (x : ℝ) (t : ℕ) (hx : 0 ≤ x)
    (h : |x-(t : ℝ)| < 1/2) : ⌊x+1/2⌋₊ = t := by
  apply (Nat.floor_eq_iff (by linarith : 0 ≤ x+1/2)).mpr
  have he := abs_lt.mp h
  constructor <;> linarith [he.1,he.2]

/-- The real-valued folded count estimate `N * foldedEstimate P z` is nonnegative. -/
theorem folded_count_nonneg (N P : ℕ) (z : Fin P) : 0 ≤ (N : ℝ)*foldedEstimate P z := by
  unfold foldedEstimate
  positivity

/-- If `N * aeEstimate P z` differs from the natural number `t` by strictly less than one half,
then `roundedCount N P z = t`. -/
theorem roundedCount_exact (N P t : ℕ) (z : Fin P)
    (h : |(N : ℝ)*aeEstimate P z-(t : ℝ)| < 1/2) : roundedCount N P z = t := by
  unfold roundedCount
  apply rounding_exact_of_half_window _ t (folded_count_nonneg N P z)
  simpa only [foldedEstimate_eq] using h

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
