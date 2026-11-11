/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary21CorrectedStat

/-!
# Positivity after diffusion in dimension at least eight

`corollary2_1Corrected` proves positivity of both updated real amplitudes for dimension N ≥ 8
under the sign and ratio hypotheses. `sqrt_le_half_dimension_sub_two` supplies the dimension
estimate used in the proof.

For the mathematical background, see [Grover1997].

## Main statements

* `corollary2_1Corrected`: For N ≥ 8, k < 0 < l and |k/l| < √N imply that both
  `distinguishedAfter N k l` and `ordinaryAfter N k l` are positive.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- For N ≥ 8, the square root of N is at most (N − 2)/2. -/
theorem sqrt_le_half_dimension_sub_two (N : ℕ) (hN : 8 ≤ N) :
    Real.sqrt N ≤ ((N : ℝ) - 2) / 2 := by
  have hn : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hpoly : 0 ≤ (N : ℝ) * ((N : ℝ) - 8) :=
    mul_nonneg (by positivity) (by linarith)
  apply (sq_le_sq₀ hs0 (show 0 ≤ ((N : ℝ) - 2) / 2 by linarith)).mp
  nlinarith

/-- For N ≥ 8, k < 0 < l and |k/l| < √N imply that both `distinguishedAfter N k l` and
`ordinaryAfter N k l` are positive. See [Grover1997]. -/
theorem corollary2_1Corrected : Corollary2_1Corrected := by
  intro N hN k l hk hl hratio
  have hn : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hnne : (N : ℝ) ≠ 0 := ne_of_gt hn0
  have habs : |k / l| = -k / l := by
    rw [abs_of_neg (div_neg_of_neg_of_pos hk hl), neg_div]
  rw [habs] at hratio
  have hbound : -k / l < ((N : ℝ) - 2) / 2 :=
    lt_of_lt_of_le hratio (sqrt_le_half_dimension_sub_two N hN)
  have hnum : 0 < 2 * k + ((N : ℝ) - 2) * l := by
    have h := (div_lt_iff₀ hl).mp hbound
    nlinarith
  have hordinary : ordinaryAfter N k l = (2 * k + ((N : ℝ) - 2) * l) / N := by
    unfold ordinaryAfter
    field_simp
  have hdistinguished : distinguishedAfter N k l =
      (((2 : ℝ) - N) * k + 2 * ((N : ℝ) - 1) * l) / N := by
    unfold distinguishedAfter
    field_simp
  constructor
  · rw [hdistinguished]
    apply div_pos _ hn0
    have hfirst : 0 < ((2 : ℝ) - N) * k := mul_pos_of_neg_of_neg (by linarith) hk
    have hsecond : 0 < 2 * ((N : ℝ) - 1) * l :=
      mul_pos (mul_pos (by norm_num) (by linarith)) hl
    linarith
  · rw [hordinary]
    exact div_pos hnum hn0

end Qatlib.Concepts.SearchStopping.KnownCount
