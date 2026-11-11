/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.AELawStability.MontanaroClaim17Stat

/-!
# An arcsine perturbation bound

This module proves `montanaroClaim17`, the arcsine perturbation inequality used in the analysis
of amplitude estimation in [Montanaro2015]. The auxiliary `arcsin_difference_bound` treats
ordered inputs in the unit interval before symmetry gives the unrestricted order.

## Main statements

* `montanaroClaim17`: bounds the change in arcsine by the square root of the difference of
  squared amplitudes.

## References

* [Montanaro, 2015, Claim 17][Montanaro2015]
-/

namespace Qatlib.Concepts.AEMeanReadout.AELawStability

/-- For `0 ≤ y ≤ x ≤ 1`, the arcsine difference is at most `π / 2` times the square root of the
absolute difference of their squares. -/
private theorem arcsin_difference_bound {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hyx : y ≤ x) :
    |Real.arcsin x - Real.arcsin y| ≤ (Real.pi / 2) * Real.sqrt |x ^ 2 - y ^ 2| := by
  let a := Real.arcsin x
  let b := Real.arcsin y
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hx0
  have hb0 : 0 ≤ b := Real.arcsin_nonneg.mpr hy0
  have ha1 : a ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have hba : b ≤ a := Real.arcsin_le_arcsin hyx
  have ht0 : 0 ≤ a - b := sub_nonneg.mpr hba
  have ht1 : a - b ≤ Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin ht0 ht1
  have hs0 : 0 ≤ Real.sin (a - b) := Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith [Real.pi_pos]⟩
  have hca : 0 ≤ Real.cos a := Real.cos_arcsin_nonneg x
  have hsb : 0 ≤ Real.sin b := by
    simpa [b, Real.sin_arcsin (by linarith : (-1 : ℝ) ≤ y) hy1] using hy0
  have hsa : Real.sin a = x := Real.sin_arcsin (by linarith) hx1
  have hsb' : Real.sin b = y := Real.sin_arcsin (by linarith) hy1
  have hid : x ^ 2 - y ^ 2 = Real.sin (a + b) * Real.sin (a - b) := by
    rw [← hsa, ← hsb', Real.sin_add, Real.sin_sub]
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]
  have horder : Real.sin (a - b) ≤ Real.sin (a + b) := by
    rw [Real.sin_add, Real.sin_sub]
    nlinarith [mul_nonneg hca hsb]
  have hsq : Real.sin (a - b) ^ 2 ≤ x ^ 2 - y ^ 2 := by
    rw [hid]
    nlinarith
  have hnonneg : 0 ≤ x ^ 2 - y ^ 2 := by nlinarith
  have hroot : Real.sin (a - b) ≤ Real.sqrt |x ^ 2 - y ^ 2| := by
    rw [abs_of_nonneg hnonneg]
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (x ^ 2 - y ^ 2)]
  have ht : a - b ≤ (Real.pi / 2) * Real.sin (a - b) := by
    have hm := mul_le_mul_of_nonneg_left hsin (Real.pi_pos.le)
    field_simp [Real.pi_ne_zero] at hm
    nlinarith
  change |a - b| ≤ _
  rw [abs_of_nonneg ht0]
  exact ht.trans (mul_le_mul_of_nonneg_left hroot (by positivity))

/-- The arcsine perturbation inequality on the unit interval, as stated in [Montanaro, Claim
17][Montanaro2015]. -/
theorem montanaroClaim17 : MontanaroClaim17 := by
  intro x y hx0 hx1 hy0 hy1
  rcases le_total y x with hyx | hxy
  · exact arcsin_difference_bound hx0 hx1 hy0 hy1 hyx
  · simpa only [abs_sub_comm] using arcsin_difference_bound hy0 hy1 hx0 hx1 hxy

end Qatlib.Concepts.AEMeanReadout.AELawStability
