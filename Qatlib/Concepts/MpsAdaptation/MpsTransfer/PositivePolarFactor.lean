/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.PositiveComplementSqrt
import Mathlib.Analysis.Normed.Ring.Units
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Classical Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable def polarUnitaryFromGram (B E : Matrix N N ℂ) : Matrix N N ℂ :=
  B * (positiveComplementSqrt E)⁻¹

theorem positive_complement_sqrt_inverse (E : Matrix N N ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hE : E.PosSemidef)
    (hcap : (q • (1 : Matrix N N ℂ)-E).PosSemidef) :
    IsUnit (positiveComplementSqrt E) ∧ ‖(positiveComplementSqrt E)⁻¹‖ ≤ 1/(1-q) := by
  let S := positiveComplementSqrt E
  have hS := positive_complement_sqrt_bounds E q hq hq1 hE hcap
  have hn : ‖(1 : Matrix N N ℂ)-S‖ ≤ q := by simpa only [norm_sub_rev] using hS.2.2.2.2
  have hunit : IsUnit S := by
    have hh := (Units.oneSub (1-S) (hn.trans_lt hq1)).isUnit
    simpa using hh
  have hdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hunit
  have he : S⁻¹=(1-S)*S⁻¹+1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_nonsing_inv S hdet]
    abel
  have hb : ‖S⁻¹‖ ≤ q*‖S⁻¹‖+1 := by
    calc
      _ = ‖(1-S)*S⁻¹+1‖ := congrArg norm he
      _ ≤ ‖(1-S)*S⁻¹‖+‖(1 : Matrix N N ℂ)‖ := norm_add_le _ _
      _ ≤ q*‖S⁻¹‖+1 := add_le_add
        ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))
        l2_norm_one_le
  refine ⟨hunit, (le_div_iff₀ (by linarith : 0 < 1-q)).mpr ?_⟩
  nlinarith

theorem positive_polar_factor (B E : Matrix N N ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hE : E.PosSemidef)
    (hcap : (q • (1 : Matrix N N ℂ)-E).PosSemidef) (hgram : B.conjTranspose*B=1-E) :
    polarUnitaryFromGram B E ∈ Matrix.unitaryGroup N ℂ ∧
    polarUnitaryFromGram B E * positiveComplementSqrt E = B := by
  let S := positiveComplementSqrt E
  have hS := positive_complement_sqrt_bounds E q hq hq1 hE hcap
  have hU := (positive_complement_sqrt_inverse E q hq hq1 hE hcap).1
  have hdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hU
  have hSi : (S⁻¹).conjTranspose=S⁻¹ := hS.1.isHermitian.inv
  have hBs : B.conjTranspose*B=S*S := hgram.trans hS.2.1.symm
  constructor
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    change (B*S⁻¹).conjTranspose*(B*S⁻¹)=1
    calc
      _ = S⁻¹*(B.conjTranspose*B)*S⁻¹ := by
        simp only [Matrix.conjTranspose_mul, hSi, Matrix.mul_assoc]
      _ = S⁻¹*(S*S)*S⁻¹ := by rw [hBs]
      _ = 1 := by
        rw [← Matrix.mul_assoc S⁻¹ S, Matrix.nonsing_inv_mul S hdet,
          Matrix.one_mul, Matrix.mul_nonsing_inv S hdet]
  · change B*S⁻¹*S=B
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hdet, Matrix.mul_one]

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
