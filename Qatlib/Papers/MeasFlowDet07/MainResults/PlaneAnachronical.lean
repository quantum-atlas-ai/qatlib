/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Matrix

namespace Qatlib.Papers.MeasFlowDet07.MainResults

def mbqcPlaneObservable (lam : MbqcPlane) (a : ℝ) : Operator 2 :=
  (Complex.ofReal (Real.cos a)) • mbqcPlaneAxisA lam
    + (Complex.ofReal (Real.sin a)) • mbqcPlaneAxisB lam

theorem mbqcPlaneBasis_eq_observable (lam : MbqcPlane) (a : ℝ) (b : Bool) :
    MbqcPlaneBasis lam a b
      = (2 : ℂ)⁻¹ • ((1 : Operator 2)
          + (if b then (-1 : ℂ) else 1) • mbqcPlaneObservable lam a) := rfl

def mbqcAnachronical : MbqcPlane → Operator 2
  | .XY => pauliZ
  | .XZ => pauliX * pauliZ
  | .YZ => pauliX

def mbqcAnachronicalSq : MbqcPlane → ℂ
  | .XY => 1
  | .XZ => -1
  | .YZ => 1

theorem mbqcAnachronical_anticomm (lam : MbqcPlane) (a : ℝ) :
    mbqcAnachronical lam * mbqcPlaneObservable lam a
      = -(mbqcPlaneObservable lam a * mbqcAnachronical lam) := by
  cases lam <;>
    simp only [mbqcAnachronical, mbqcPlaneObservable, mbqcPlaneAxisA, mbqcPlaneAxisB] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem mbqcAnachronical_sq (lam : MbqcPlane) :
    mbqcAnachronical lam * mbqcAnachronical lam
      = mbqcAnachronicalSq lam • (1 : Operator 2) := by
  cases lam
  · simp only [mbqcAnachronical, mbqcAnachronicalSq, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [mbqcAnachronical, mbqcAnachronicalSq, neg_smul, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [mbqcAnachronical, mbqcAnachronicalSq, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem conj_core_plus {C M : Operator 2} {δ : ℂ}
    (hCM : C * M = -(M * C)) (hC2 : C * C = δ • (1 : Operator 2)) :
    C * ((1 : Operator 2) + (1 : ℂ) • M) * C
      = δ • ((1 : Operator 2) + (-1 : ℂ) • M) := by
  have h2 : (C * M) * C = -(δ • M) := by
    rw [hCM, Matrix.neg_mul, Matrix.mul_assoc, hC2, Matrix.mul_smul, Matrix.mul_one]
  calc C * ((1 : Operator 2) + (1 : ℂ) • M) * C
      = (C + (C * M)) * C := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, one_smul]
    _ = C * C + (C * M) * C := by rw [Matrix.add_mul]
    _ = δ • (1 : Operator 2) - δ • M := by rw [hC2, h2, sub_eq_add_neg]
    _ = δ • ((1 : Operator 2) + (-1 : ℂ) • M) := by
        rw [smul_add, sub_eq_add_neg, smul_smul, mul_neg, mul_one, ← neg_smul]

theorem conj_core_minus {C M : Operator 2} {δ : ℂ}
    (hCM : C * M = -(M * C)) (hC2 : C * C = δ • (1 : Operator 2)) :
    C * ((1 : Operator 2) + (-1 : ℂ) • M) * C
      = δ • ((1 : Operator 2) + (1 : ℂ) • M) := by
  have h2 : (C * M) * C = -(δ • M) := by
    rw [hCM, Matrix.neg_mul, Matrix.mul_assoc, hC2, Matrix.mul_smul, Matrix.mul_one]
  calc C * ((1 : Operator 2) + (-1 : ℂ) • M) * C
      = (C + (-(C * M))) * C := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, neg_smul, one_smul]
    _ = C * C + (-(C * M)) * C := by rw [Matrix.add_mul]
    _ = δ • (1 : Operator 2) + δ • M := by rw [hC2, Matrix.neg_mul, h2, neg_neg]
    _ = δ • ((1 : Operator 2) + (1 : ℂ) • M) := by
        rw [smul_add, one_smul]

theorem conj_proj_plus {C M : Operator 2} {δ : ℂ}
    (hCM : C * M = -(M * C)) (hC2 : C * C = δ • (1 : Operator 2)) :
    C * ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (1 : ℂ) • M)) * C
      = δ • ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (-1 : ℂ) • M)) := by
  calc C * ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (1 : ℂ) • M)) * C
      = (2 : ℂ)⁻¹ • (C * ((1 : Operator 2) + (1 : ℂ) • M) * C) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (2 : ℂ)⁻¹ • (δ • ((1 : Operator 2) + (-1 : ℂ) • M)) := by rw [conj_core_plus hCM hC2]
    _ = δ • ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (-1 : ℂ) • M)) := by rw [smul_comm]

theorem conj_proj_minus {C M : Operator 2} {δ : ℂ}
    (hCM : C * M = -(M * C)) (hC2 : C * C = δ • (1 : Operator 2)) :
    C * ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (-1 : ℂ) • M)) * C
      = δ • ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (1 : ℂ) • M)) := by
  calc C * ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (-1 : ℂ) • M)) * C
      = (2 : ℂ)⁻¹ • (C * ((1 : Operator 2) + (-1 : ℂ) • M) * C) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (2 : ℂ)⁻¹ • (δ • ((1 : Operator 2) + (1 : ℂ) • M)) := by rw [conj_core_minus hCM hC2]
    _ = δ • ((2 : ℂ)⁻¹ • ((1 : Operator 2) + (1 : ℂ) • M)) := by rw [smul_comm]

theorem mbqcPlaneBasis_conj_anachronical (lam : MbqcPlane) (a : ℝ) (b : Bool) :
    mbqcAnachronical lam * MbqcPlaneBasis lam a b * mbqcAnachronical lam
      = mbqcAnachronicalSq lam • MbqcPlaneBasis lam a (!b) := by
  have hcm := mbqcAnachronical_anticomm lam a
  have hsq := mbqcAnachronical_sq lam
  cases b
  · simp only [Bool.not_false]
    rw [mbqcPlaneBasis_eq_observable (b := false), mbqcPlaneBasis_eq_observable (b := true)]
    simp only [Bool.false_eq_true, if_false, if_true]
    exact conj_proj_plus hcm hsq
  · simp only [Bool.not_true]
    rw [mbqcPlaneBasis_eq_observable (b := true), mbqcPlaneBasis_eq_observable (b := false)]
    simp only [Bool.false_eq_true, if_false, if_true]
    exact conj_proj_minus hcm hsq

theorem projection_mul_axis {M : Operator 2} (hM : M * M = 1) {s : ℂ} (hs : s * s = 1) :
    ((2 : ℂ)⁻¹ • ((1 : Operator 2) + s • M)) * M
      = s • ((2 : ℂ)⁻¹ • ((1 : Operator 2) + s • M)) := by
  have hleft : ((2 : ℂ)⁻¹ • ((1 : Operator 2) + s • M)) * M
      = (2 : ℂ)⁻¹ • (M + s • (1 : Operator 2)) := by
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hM]
  have hright : s • ((2 : ℂ)⁻¹ • ((1 : Operator 2) + s • M))
      = (2 : ℂ)⁻¹ • (M + s • (1 : Operator 2)) := by
    rw [smul_comm, smul_add, smul_smul, hs, one_smul, add_comm]
  rw [hleft, hright]

theorem pauliZ_sq : pauliZ * pauliZ = (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX_sq : pauliX * pauliX = (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_sq : pauliY * pauliY = (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem mbqcPlaneObservable_XZ_zero :
    mbqcPlaneObservable .XZ 0 = pauliZ := by
  simp [mbqcPlaneObservable, mbqcPlaneAxisA, mbqcPlaneAxisB, Real.cos_zero, Real.sin_zero]

theorem mbqcPlaneObservable_XZ_pi_div_two :
    mbqcPlaneObservable .XZ (Real.pi / 2) = pauliX := by
  simp [mbqcPlaneObservable, mbqcPlaneAxisA, mbqcPlaneAxisB, Real.cos_pi_div_two,
    Real.sin_pi_div_two]

theorem mbqcPlaneObservable_XY_pi_div_two :
    mbqcPlaneObservable .XY (Real.pi / 2) = pauliY := by
  simp [mbqcPlaneObservable, mbqcPlaneAxisA, mbqcPlaneAxisB, Real.cos_pi_div_two,
    Real.sin_pi_div_two]

theorem mbqcPlaneBasis_pauliZ (b : Bool) :
    MbqcPlaneBasis .XZ 0 b * pauliZ
      = (if b then (-1 : ℂ) else 1) • MbqcPlaneBasis .XZ 0 b := by
  rw [mbqcPlaneBasis_eq_observable, mbqcPlaneObservable_XZ_zero]
  exact projection_mul_axis pauliZ_sq (s := if b then (-1 : ℂ) else 1) (by cases b <;> simp)

theorem mbqcPlaneBasis_pauliX (b : Bool) :
    MbqcPlaneBasis .XZ (Real.pi / 2) b * pauliX
      = (if b then (-1 : ℂ) else 1) • MbqcPlaneBasis .XZ (Real.pi / 2) b := by
  rw [mbqcPlaneBasis_eq_observable, mbqcPlaneObservable_XZ_pi_div_two]
  exact projection_mul_axis pauliX_sq (s := if b then (-1 : ℂ) else 1) (by cases b <;> simp)

theorem mbqcPlaneBasis_pauliY (b : Bool) :
    MbqcPlaneBasis .XY (Real.pi / 2) b * pauliY
      = (if b then (-1 : ℂ) else 1) • MbqcPlaneBasis .XY (Real.pi / 2) b := by
  rw [mbqcPlaneBasis_eq_observable, mbqcPlaneObservable_XY_pi_div_two]
  exact projection_mul_axis pauliY_sq (s := if b then (-1 : ℂ) else 1) (by cases b <;> simp)

theorem pauliX_mul_pauliZ : pauliX * pauliZ = (-Complex.I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem mbqcPlaneBasis_pauliY_mul_XZ (b : Bool) :
    MbqcPlaneBasis .XY (Real.pi / 2) b * (pauliX * pauliZ)
      = (if b then Complex.I else -Complex.I) • MbqcPlaneBasis .XY (Real.pi / 2) b := by
  have hY := mbqcPlaneBasis_pauliY b
  rw [pauliX_mul_pauliZ, Matrix.mul_smul, hY, smul_smul]
  congr 1
  cases b <;> simp

end Qatlib.Papers.MeasFlowDet07.MainResults
