/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdaptiveTest26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Typicality Factor Concentration Around Unity

This module proves Lemma 7.4: when the typicality exponent `E` satisfies `|E| ≤ 2 c_N`
with `0 < c_N ≤ 1 / 16`, the typicality factor `gTypical E = exp(E)` lies in
`[1 - 4 c_N, 1 + 4 c_N]`.

## Main statements

* `typicality_factor`: two-sided interval bound `gTypical E ∈ [1 - 4 c_N, 1 + 4 c_N]`.

## References

* [Seyfried et al., 2026][SeyfriedSenTomamichel2026], Lemma 7.4, Eq. (261), p. 43.
-/

namespace Qatlib.Papers.AdaptiveTest26.MainResults.LowerBound

open Qatlib.Papers.AdaptiveTest26.MainResults

set_option autoImplicit false
noncomputable section

/-- **Lemma 7.4 (Typicality factor)**: if `|E| ≤ 2 c_N` and `0 < c_N ≤ 1 / 16`, then
`gTypical E ∈ Set.Icc (1 - 4 * cN) (1 + 4 * cN)`. -/
theorem typicality_factor (cN : ℝ) (hcN : 0 < cN) (hsmall : cN ≤ 1 / 16)
    (E : ℝ) (hE : |E| ≤ 2 * cN) :
    gTypical E ∈ Set.Icc (1 - 4 * cN) (1 + 4 * cN) := by
  change 1 - 4 * cN ≤ Real.exp E ∧ Real.exp E ≤ 1 + 4 * cN
  rcases abs_le.mp hE with ⟨hElo, hEhi⟩
  constructor
  · linarith [Real.add_one_le_exp E]
  · have hexp := Real.exp_pos E
    have hprod : Real.exp E * (1 - E) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-E)) hexp.le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
      nlinarith only [h]
    have hbound : Real.exp E * (1 - 2 * cN) ≤ 1 := by
      nlinarith [mul_nonneg hexp.le (sub_nonneg.mpr hEhi)]
    have hquadratic : 1 ≤ (1 + 4 * cN) * (1 - 2 * cN) := by
      nlinarith [mul_nonneg hcN.le (show 0 ≤ 1 - 4 * cN by linarith)]
    have hpos : 0 < 1 - 2 * cN := by linarith
    exact (mul_le_mul_iff_left₀ hpos).mp (hbound.trans hquadratic)

end

end Qatlib.Papers.AdaptiveTest26.MainResults.LowerBound
