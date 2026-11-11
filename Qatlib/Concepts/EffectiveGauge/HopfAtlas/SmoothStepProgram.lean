/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.NegativeExpProgram
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # The rational smooth_step program approximates the actual native cutoff -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rational Smooth Step in the Hopf Atlas construction. -/
def rationalSmoothStep (x tolerance : ℚ) : RationalScalarResult :=
  if x ≤ 0 then ⟨0,0,0⟩
  else if 1 ≤ x then ⟨1,0,0⟩
  else
    let e := min (1/64) (tolerance/1024)
    let a := rationalNegativeExp (1/x) e
    let b := rationalNegativeExp (1/(1-x)) e
    ⟨a.value/(a.value+b.value),384*max a.error b.error,a.terms+b.terms⟩

noncomputable section

/-- Original `exp_neg_two_lower` guarantee for the `SmoothStepProgram` construction; the complete source hypotheses are retained. -/
private theorem exp_neg_two_lower : (1/8 : ℝ) ≤ Real.exp (-2) := by
  have h1 : Real.exp 1<11/4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h2 : Real.exp 2<8 := by
    have he : Real.exp 2=(Real.exp 1)^2 := by simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul 1 2
    rw [he]
    nlinarith [Real.exp_pos 1]
  rw [Real.exp_neg]
  simpa only [one_div] using (one_div_le_one_div_of_le (Real.exp_pos 2) h2.le)

/-- Original `smoothStep_sum_lower` guarantee for the `SmoothStepProgram` construction; the complete source hypotheses are retained. -/
private theorem smoothStep_sum_lower (x : ℝ) (hx : 0<x) :
    (1/8 : ℝ) ≤ Real.exp (-x⁻¹)+Real.exp (-(1-x)⁻¹) := by
  by_cases hh : 1/2 ≤ x
  · have hi : x⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hx).mpr (by linarith)
    exact (exp_neg_two_lower.trans (Real.exp_le_exp.mpr (by linarith))).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hi : (1-x)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ (by linarith : 0<1-x)).mpr (by linarith)
    exact (exp_neg_two_lower.trans (Real.exp_le_exp.mpr (by linarith))).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- The approximate denominator has a fixed positive margin. The returned
ratio error uses the actual maximum exponential error, not their tolerance. -/
private theorem smoothStep_ratio_error (a b A B E : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : A ∈ Set.Icc 0 1) (hB : B ∈ Set.Icc 0 1) (hsum : 1/8 ≤ A+B)
    (hE : 0 ≤ E) (hEs : E ≤ 1/64) (hae : |a-A| ≤ E) (hbe : |b-B| ≤ E) :
    1/16 ≤ a+b ∧ |a/(a+b)-A/(A+B)| ≤ 384*E := by
  have hden : 1/16 ≤ a+b := by
    have h1 := abs_le.mp hae
    have h2 := abs_le.mp hbe
    linarith
  refine ⟨hden,?_⟩
  have hd : 0<a+b := by linarith
  have hD : 0<A+B := by linarith
  have hnum : |a*B-A*b| ≤ 2*E := by
    calc
      _ = |(a-A)*B+A*(B-b)| := by congr 1; ring
      _ ≤ |(a-A)*B|+|A*(B-b)| := abs_add_le _ _
      _ = |a-A| *B+A*|b-B| := by rw [abs_mul,abs_mul,abs_of_nonneg hB.1,abs_of_nonneg hA.1,abs_sub_comm B b]
      _ ≤ E*1+1*E := add_le_add (mul_le_mul hae hB.2 hB.1 hE) (mul_le_mul hA.2 hbe (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hp : 1/128 ≤ (a+b)*(A+B) := by nlinarith
  have hid : a/(a+b)-A/(A+B)=(a*B-A*b)/((a+b)*(A+B)) := by field_simp; ring
  rw [hid,abs_div,abs_of_pos (mul_pos hd hD)]
  calc
    _ ≤ (2*E)/((a+b)*(A+B)) := div_le_div_of_nonneg_right hnum (mul_pos hd hD).le
    _ ≤ (2*E)/(1/128) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
    _ ≤ 384*E := by linarith

/-- Same rational ratio and error as smooth_step, including its two exact
outer branches. There is no supplied cutoff oracle. -/
theorem rationalSmoothStep_spec (x tolerance : ℚ) (ht : 0<tolerance) :
    let r := rationalSmoothStep x tolerance
    |(r.value : ℝ)-Real.smoothTransition (x : ℝ)| ≤ (r.error : ℝ) ∧
      0 ≤ r.value ∧ r.value ≤ 1 ∧ 0 ≤ r.error ∧ r.error ≤ tolerance := by
  dsimp only [rationalSmoothStep]
  split_ifs with hx hx1
  · dsimp only
    have hz := Real.smoothTransition.zero_of_nonpos (by exact_mod_cast hx : (x : ℝ) ≤ 0)
    simp only [hz,Rat.cast_zero,sub_self,abs_zero,le_refl,zero_le_one,true_and]
    exact ht.le
  · dsimp only
    have hz := Real.smoothTransition.one_of_one_le (by exact_mod_cast hx1 : (1 : ℝ) ≤ x)
    simp only [hz,Rat.cast_one,sub_self,abs_zero,Rat.cast_zero,le_refl,zero_le_one,true_and]
    exact ht.le
  · let e : ℚ := min (1/64) (tolerance/1024)
    let a := rationalNegativeExp (1/x) e
    let b := rationalNegativeExp (1/(1-x)) e
    let A := Real.exp (-((1/x : ℚ) : ℝ))
    let B := Real.exp (-((1/(1-x) : ℚ) : ℝ))
    let E : ℚ := max a.error b.error
    have hx0 : 0<x := lt_of_not_ge hx
    have hxlt : x<1 := lt_of_not_ge hx1
    have hxR : (0 : ℝ)<x := by exact_mod_cast hx0
    have hx1R : (x : ℝ)<1 := by exact_mod_cast hxlt
    have he : 0<e := lt_min (by norm_num) (by positivity)
    have ha := rationalNegativeExp_spec (1/x) e (by positivity) he
    have hb := rationalNegativeExp_spec (1/(1-x)) e (by positivity) he
    have hAx : (0 : ℝ) ≤ ((1/x : ℚ) : ℝ) := by exact_mod_cast (one_div_nonneg.mpr hx0.le)
    have hBx : (0 : ℝ) ≤ ((1/(1-x) : ℚ) : ℝ) := by exact_mod_cast (one_div_nonneg.mpr (show (0 : ℚ) ≤ 1-x by linarith))
    have hA : A ∈ Set.Icc 0 1 := ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hAx)⟩
    have hB : B ∈ Set.Icc 0 1 := ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hBx)⟩
    have hE0 : 0 ≤ E := le_max_of_le_left ha.2.2.2.1
    have hEe : E ≤ e := max_le ha.2.2.2.2.1 hb.2.2.2.2.1
    have hE64 : E ≤ 1/64 := hEe.trans (min_le_left _ _)
    have hsum : 1/8 ≤ A+B := by
      simpa only [A,B,Rat.cast_div,Rat.cast_one,Rat.cast_sub,one_div,Rat.cast_inv] using smoothStep_sum_lower (x : ℝ) hxR
    have htarget : Real.smoothTransition (x : ℝ)=A/(A+B) := by
      simp only [Real.smoothTransition,expNegInvGlue,if_neg (not_le.mpr hxR),if_neg (not_le.mpr (show 0<1-(x : ℝ) by linarith)),
        A,B,Rat.cast_one,Rat.cast_sub,one_div,Rat.cast_inv]
    have hE64R : (E : ℝ) ≤ 1/64 := by
      have hh : (E : ℝ) ≤ (((1/64 : ℚ) : ℝ)) := Rat.cast_le.mpr hE64
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hh
      exact hh
    have hratio := smoothStep_ratio_error (a.value : ℝ) (b.value : ℝ) A B (E : ℝ)
      (by exact_mod_cast ha.2.1) (by exact_mod_cast hb.2.1) hA hB hsum
      (by exact_mod_cast hE0) hE64R
      (ha.1.trans (by exact_mod_cast le_max_left a.error b.error))
      (hb.1.trans (by exact_mod_cast le_max_right a.error b.error))
    have hden : 0<a.value+b.value := by
      have hR : (0 : ℝ)<(a.value+b.value : ℚ) := by push_cast; linarith [hratio.1]
      exact_mod_cast hR
    change |((a.value/(a.value+b.value) : ℚ) : ℝ)-Real.smoothTransition (x : ℝ)| ≤ ((384*E : ℚ) : ℝ) ∧
      0 ≤ a.value/(a.value+b.value) ∧ a.value/(a.value+b.value) ≤ 1 ∧ 0 ≤ 384*E ∧ 384*E ≤ tolerance
    refine ⟨?_,div_nonneg ha.2.1 (add_nonneg ha.2.1 hb.2.1),?_,by positivity,?_⟩
    · rw [htarget]
      push_cast
      exact hratio.2
    · apply (div_le_one₀ hden).mpr
      linarith [hb.2.1]
    · have hEt : E ≤ tolerance/1024 := hEe.trans (min_le_right _ _)
      linarith

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
