/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation15Stat
import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation14Simu
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix
open scoped Classical Matrix.Norms.L2Operator

theorem oaa_scale_defect_le (s δ : ℝ) (hs : 1 ≤ s) (hd : |s-2| ≤ δ) (hδ : δ ≤ 1) :
    |3/s-4/s^3-1| ≤ 15*δ := by
  have hspos : 0 < s := by linarith
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hd
  have hs3 : s ≤ 3 := by have hh := (abs_le.mp hd).2; linarith
  have hpow : 1 ≤ s^3 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs 3
  have he : 3/s-4/s^3-1=-((s-2)^2*(s+1)/s^3) := by field_simp; ring
  rw [he, abs_neg, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (pow_pos hspos 3)).mpr
  have hsq : (s-2)^2 ≤ |s-2| := by
    have hh : |s-2| ≤ 1 := hd.trans hδ
    nlinarith [sq_abs (s-2), abs_nonneg (s-2)]
  calc
    _ ≤ (s-2)^2*4 := mul_le_mul_of_nonneg_left (by linarith : s+1 ≤ 4) (sq_nonneg _)
    _ ≤ |s-2| * 4 := mul_le_mul_of_nonneg_right hsq (by norm_num)
    _ ≤ δ*4 := mul_le_mul_of_nonneg_right hd (by norm_num)
    _ ≤ 15*δ := by linarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 15*δ)]

theorem oaa_cubic_operator_error_le {I : Type*} [Fintype I] [DecidableEq I]
    (X U : Matrix I I ℂ) (s δ₁ δ₂ : ℝ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (hX : ‖X-U‖ ≤ δ₁) (hs : 1 ≤ s) (hd : |s-2| ≤ δ₂) (hδ : δ₂ ≤ 1) :
    ‖((3/s : ℝ) : ℂ) • X-((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X)-U‖ ≤
      (15+12*δ₁+4*δ₁^2)*δ₁+15*δ₂ := by
  have hδ₁ : 0 ≤ δ₁ := (norm_nonneg _).trans hX
  have hspos : 0 < s := by linarith
  have hpow : 1 ≤ s^3 := by simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs 3
  have ha : ‖((3/s : ℝ) : ℂ)‖ ≤ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hspos).mpr (by linarith)
  have hb : ‖((4/s^3 : ℝ) : ℂ)‖ ≤ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ (pow_pos hspos 3)).mpr (by linarith)
  have hdC : ‖((3/s : ℝ) : ℂ)-((4/s^3 : ℝ) : ℂ)-1‖ ≤ 15*δ₂ := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact oaa_scale_defect_le s δ₂ hs hd hδ
  let D : Matrix I I ℂ := ((3/s : ℝ) : ℂ) • X-
    ((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X)-U
  have hD : ‖D‖ ≤ (15+12*δ₁+4*δ₁^2)*δ₁+15*δ₂ := by
    have hh := l2_norm_scaled_cubic_sub_unitary_le hU hX
      ((3/s : ℝ) : ℂ) ((4/s^3 : ℝ) : ℂ)
    have hp : 0 ≤ 3+3*δ₁+δ₁^2 := by positivity
    have hcoef := add_le_add ha (mul_le_mul_of_nonneg_right hb hp)
    have hmul := mul_le_mul_of_nonneg_right hcoef hδ₁
    exact hh.trans (by nlinarith)
  exact hD

theorem equation15 : Equation15 := by
  intro J I _ _ _ _ W j₀ X U s δ₁ δ₂ hW hU hX hs hd hδ ψ hψ
  let D : Matrix I I ℂ := ((3/s : ℝ) : ℂ) • X-
    ((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X)-U
  have hD := oaa_cubic_operator_error_le X U s δ₁ δ₂ hU hX hs hd hδ
  rw [equation14 J I W j₀ X s hW ψ]
  have he : TensorState (Ket j₀)
      ((((3/s : ℝ) : ℂ) • X-((4/s^3 : ℝ) : ℂ) • (X*Xᴴ*X)) *ᵥ ψ)-
      TensorState (Ket j₀) (U *ᵥ ψ)=TensorState (Ket j₀) (D *ᵥ ψ) := by
    simp only [D, Matrix.sub_mulVec]
    funext p
    simp only [Pi.sub_apply, TensorState]
    ring
  rw [he, tensorState_l2_norm,
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j₀), one_mul]
  have hv := l2_norm_mulVec_fromVec_le D ψ
  rw [(normalized_iff_norm_toEuclidean_fromVec _).mp hψ, mul_one] at hv
  exact hv.trans hD

end Qatlib.Concepts.CoherentSim.ResetDiscard
