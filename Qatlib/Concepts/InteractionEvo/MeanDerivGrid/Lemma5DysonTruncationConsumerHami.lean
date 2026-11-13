/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonTruncationConsumerStat
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.Lemma5DysonSourceParametersHami

/-!
# A two-level Dyson grid approximation

`lemma5DysonTruncationConsumer` instantiates the source-parameter estimate for
`interactionPictureField`. It certifies an operator-norm error of at most 1/8 at time 2/5 using
38 grid points and truncation order 3. These estimates support the interaction-picture
simulation analysis of [LowWiebe2018].

## Main statements

* `lemma5DysonTruncationConsumer`: the concrete two-level error certificate.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Bounds the error of the order-3, 38-point Dyson grid sum for `interactionPictureField` at
time 2/5 by 1/8, as an instance of [Low and Wiebe, Lemma 5][LowWiebe2018]. -/
theorem lemma5DysonTruncationConsumer : Lemma5DysonTruncationConsumer := by
  let Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]
  let X : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0,1], ![1,0]]
  have hZherm : Z.IsHermitian := by
    change Zᴴ = Z
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Z, Matrix.conjTranspose_apply]
  have hXherm : X.IsHermitian := by
    change Xᴴ = X
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [X, Matrix.conjTranspose_apply]
  have hZunit : Z ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Zᴴ * Z = 1
    rw [hZherm]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Z, Matrix.mul_apply, Fin.sum_univ_two]
  have hXunit : X ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Xᴴ * X = 1
    rw [hXherm]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [X, Matrix.mul_apply, Fin.sum_univ_two]
  have hZ := l2_norm_unitary_le_one hZunit
  have hX := l2_norm_unitary_le_one hXunit
  let Hd : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => (1/4 : ℝ) • Z
  have hderiv (u : ℝ) : HasDerivAt interactionPictureField (Hd u) u := by
    convert! ((((hasDerivAt_id u).div_const 4).const_add 1).smul_const Z).add_const
      ((3/20 : ℝ) • X) using 1
  have hH : Continuous interactionPictureField :=
    continuous_iff_continuousAt.mpr (fun u => (hderiv u).continuousAt)
  have hHerm (u : ℝ) : (interactionPictureField u).IsHermitian :=
    (hZherm.smul (show IsSelfAdjoint (1+u/4 : ℝ) from rfl)).add
      (hXherm.smul (show IsSelfAdjoint (3/20 : ℝ) from rfl))
  have hbound (u : ℝ) (hu : u ∈ Set.Icc 0 (2/5 : ℝ)) :
      (interactionPictureField u).IsHermitian ∧ ‖interactionPictureField u‖ ≤ (5/4 : ℝ) := by
    refine ⟨hHerm u, ?_⟩
    change ‖(1+u/4 : ℝ) • Z+(3/20 : ℝ) • X‖ ≤ _
    have hr : 0 ≤ 1+u/4 := by linarith [hu.1]
    calc
      _ ≤ ‖(1+u/4 : ℝ) • Z‖+‖(3/20 : ℝ) • X‖ := norm_add_le _ _
      _ = (1+u/4)*‖Z‖+(3/20)*‖X‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
        norm_num
      _ ≤ (1+u/4)+(3/20) := by
        apply add_le_add
        · simpa only [mul_one] using! mul_le_mul_of_nonneg_left hZ hr
        · simpa only [mul_one] using! mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 3/20)
      _ ≤ 5/4 := by linarith [hu.2]
  have hD : ‖(1/4 : ℝ) • Z‖ ≤ (1/4 : ℝ) := by
    simpa [norm_smul, Real.norm_eq_abs] using!
        mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 1/4)
  have hlog : (5/4 : ℝ)*(2/5) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hgrid : (16 : ℝ)*(2/5)^2*((1/(2/5))*∫ u in (0 : ℝ)..(2/5), ‖Hd u‖+(5/4)^2)/(1/8) ≤ 38 := by
    norm_num [Hd, intervalIntegral.integral_const, smul_eq_mul]
    nlinarith [hD]
  unfold Lemma5DysonTruncationConsumer
  exact lemma5DysonSourceParameters (Fin 2) interactionPictureField Hd (2/5) (5/4) (1/8) 3 38
    hH continuous_const (fun u _ => hderiv u) (by norm_num) (by norm_num) (by norm_num)
    hbound hlog hgrid (by norm_num [Nat.factorial])

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
