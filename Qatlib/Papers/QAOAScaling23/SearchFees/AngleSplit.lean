/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.FeeRecurrence

/-!
# Low-mass amplification angle comparisons

For an amplification angle in the first quadrant with marked mass at most one half,
`lowQ_double_sine` compares its sine with the doubled-angle sine. This comparison transfers a
source cap condition to the doubled-angle condition used in the geometric-search bounds.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `lowQ_double_sine`: If `0 < θ < π/2` and `sin θ` squared is at most `1/2`, then `sin θ ≤ sin
  (2 * θ)`.
* `lowQ_source_cap`: Under the low-mass angle hypotheses, the cap condition `M * sin θ ≥ 1`
  implies `M * sin (2 * θ) ≥ 1`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.SearchFees

/-- If `0 < θ < π/2` and `sin θ` squared is at most `1/2`, then `sin θ ≤ sin (2 * θ)`. -/
theorem lowQ_double_sine (θ:ℝ) (h0:0<θ) (h1:θ<Real.pi/2) (hQ:(Real.sin θ)^2≤1/2) :
    Real.sin θ≤Real.sin (2*θ) := by
  have hs:0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc:0<Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],h1⟩
  have hid:=Real.sin_sq_add_cos_sq θ
  have hh:(1/2:ℝ)≤Real.cos θ := by nlinarith
  rw [Real.sin_two_mul]
  nlinarith

/-- Under the low-mass angle hypotheses, the cap condition `M * sin θ ≥ 1` implies `M * sin (2 *
θ) ≥ 1`. -/
theorem lowQ_source_cap (M:ℕ) (θ:ℝ) (h0:0<θ) (h1:θ<Real.pi/2)
    (hQ:(Real.sin θ)^2≤1/2) (hcap:1≤(M:ℝ)*Real.sin θ) :
    1≤(M:ℝ)*Real.sin (2*θ) :=
  hcap.trans (mul_le_mul_of_nonneg_left (lowQ_double_sine θ h0 h1 hQ) (Nat.cast_nonneg M))
end Qatlib.Papers.QAOAScaling23.SearchFees
