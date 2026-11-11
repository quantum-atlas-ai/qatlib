/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SeedSqrt
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeedChart

/-! # Finite rational initial seeds on the fixed certified chart -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of seed Value Precision in the Rational Flow construction. -/
def seedValuePrecision (tolerance : ℚ) : ℕ := max 8 (Nat.clog 2 (Nat.ceil (32/tolerance)))

/-- Definition of rational Chart Seed in the Rational Flow construction. -/
def rationalChartSeed (chart : SeedChart) (s : Fin 3 → ℚ) (b : ℕ) : Quaternion ℚ :=
  match chart with
  | .north =>
    let a := seedSqrtFloor ((1+s 0)/2) b
    ⟨a,0,s 2/(2*a),-s 1/(2*a)⟩
  | .south =>
    let a := seedSqrtFloor ((1-s 0)/2) b
    ⟨s 2/(2*a),s 1/(2*a),a,0⟩

/-- Definition of origin Seed On Chart in the Rational Flow construction. -/
def originSeedOnChart (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (chart : SeedChart) (tolerance : ℚ) : Quaternion ℚ :=
  rationalChartSeed chart (originSpinSamples source (seedValuePrecision tolerance))
    (seedValuePrecision tolerance)

/-- Definition of origin Seed Approximation in the Rational Flow construction. -/
def originSeedApproximation (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (tolerance : ℚ) : Quaternion ℚ :=
  originSeedOnChart source (chosenOriginChart source) tolerance

/-- Original `seedValuePrecision_eight` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem seedValuePrecision_eight (tolerance : ℚ) : 8 ≤ seedValuePrecision tolerance := le_max_left _ _

/-- Original `seedValuePrecision_budget` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem seedValuePrecision_budget (tolerance : ℚ) (ht : 0<tolerance) :
    32*(2^seedValuePrecision tolerance : ℚ)⁻¹ ≤ tolerance := by
  have hpow : Nat.ceil (32/tolerance) ≤ 2^seedValuePrecision tolerance :=
    (Nat.clog_le_iff_le_pow (by decide)).mp (le_max_right _ _)
  have h : 32/tolerance ≤ (2^seedValuePrecision tolerance : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpow)
  apply (mul_inv_le_iff₀ (by positivity : (0 : ℚ)<2^seedValuePrecision tolerance)).mpr
  simpa only [mul_comm] using (div_le_iff₀ ht).mp h

noncomputable section
open scoped Quaternion

/-- Original `seed_dyadic_small` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem seed_dyadic_small (b : ℕ) (hb : 8 ≤ b) : (2^b : ℝ)⁻¹ ≤ (1/256 : ℝ) := by
  have h : (256 : ℝ) ≤ 2^b := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) hb)
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<256) h

/-- Original `seedRoot_error` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem seedRoot_error (u : ℚ) (z : ℝ) (b : ℕ) (hb : 8 ≤ b) (hc : -(1/2 : ℝ)<z)
    (he : |(u : ℝ)-z| ≤ (2^b : ℝ)⁻¹) :
    (1/4 : ℝ) ≤ (seedSqrtFloor ((1+u)/2) b : ℝ) ∧
      |(seedSqrtFloor ((1+u)/2) b : ℝ)-Real.sqrt ((1+z)/2)| ≤ 2*(2^b : ℝ)⁻¹ := by
  let e : ℝ := (2^b : ℝ)⁻¹
  let a : ℝ := (seedSqrtFloor ((1+u)/2) b : ℝ)
  let A := Real.sqrt ((1+z)/2)
  let B := Real.sqrt (((1+u)/2 : ℚ) : ℝ)
  change |(u : ℝ)-z| ≤ e at he
  have he0 : 0 ≤ e := by positivity
  have hes : e ≤ 1/256 := seed_dyadic_small b hb
  have hz : 0 ≤ (1+z)/2 := by linarith
  have huR : (0 : ℝ) ≤ (((1+u)/2 : ℚ) : ℝ) := by
    push_cast
    linarith [(abs_le.mp he).1]
  have hu : (0 : ℚ) ≤ (1+u)/2 := Rat.cast_nonneg.mp huR
  have hAsq : A^2=(1+z)/2 := Real.sq_sqrt hz
  have hBsq : B^2=(1+(u : ℝ))/2 := by simpa only [B,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat] using Real.sq_sqrt huR
  have hAn : 0 ≤ A := Real.sqrt_nonneg _
  have hBn : 0 ≤ B := Real.sqrt_nonneg _
  have hA : (1/2 : ℝ)<A := by
    apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/2) hAn).mp
    rw [hAsq]
    linarith
  have harg : |B^2-A^2| ≤ e/2 := by
    calc
      _ = |((u : ℝ)-z)/2| := by congr 1; rw [hBsq,hAsq]; ring
      _ = |(u : ℝ)-z|/2 := by rw [abs_div]; norm_num
      _ ≤ e/2 := div_le_div_of_nonneg_right he (by norm_num)
  have hid : |B-A| * (B+A)=|B^2-A^2| := by
    rw [← abs_of_nonneg (add_nonneg hBn hAn),← abs_mul]
    congr 1
    ring
  have hBA : |B-A| ≤ e := by
    have h := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ B+A by linarith) (abs_nonneg (B-A))
    rw [hid] at h
    linarith
  have hf := seedSqrtFloor_bounds ((1+u)/2) hu b
  have hfa : |a-B| ≤ e := by rw [abs_of_nonpos (sub_nonpos.mpr hf.1)]; linarith [hf.2]
  have hdelta : |a-A| ≤ 2*e := by
    calc
      _ ≤ |a-B|+|B-A| := by simpa only [Real.dist_eq] using dist_triangle a B A
      _ ≤ e+e := add_le_add hfa hBA
      _ = _ := by ring
  exact ⟨by have h := (abs_le.mp hdelta).1; linarith,hdelta⟩

/-- Original `seedQuotient_error` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem seedQuotient_error (n a : ℚ) (N A e : ℝ) (he : 0 ≤ e)
    (ha : (1/4 : ℝ) ≤ (a : ℝ)) (hA : (1/2 : ℝ) ≤ A) (hN : |N| ≤ 1)
    (hn : |(n : ℝ)-N| ≤ e) (hd : |(a : ℝ)-A| ≤ 2*e) :
    |(n : ℝ)/(2*(a : ℝ))-N/(2*A)| ≤ 10*e := by
  have hap : (0 : ℝ)<a := by linarith
  have hAp : 0<A := by linarith
  have hden : (1/4 : ℝ) ≤ 2*(a : ℝ)*A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hA)]
  have hid : (n : ℝ)/(2*(a : ℝ))-N/(2*A)=
      ((n : ℝ)-N)/(2*(a : ℝ))+N*(A-(a : ℝ))/(2*(a : ℝ)*A) := by field_simp; ring
  have hfirst : |((n : ℝ)-N)/(2*(a : ℝ))| ≤ 2*e := by
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<2*(a : ℝ))]
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_nonneg he (sub_nonneg.mpr ha)
    nlinarith
  have hsecond : |N*(A-(a : ℝ))/(2*(a : ℝ)*A)| ≤ 8*e := by
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<2*(a : ℝ)*A)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hnumer : |N*(A-(a : ℝ))| ≤ 2*e := by
      rw [abs_mul,abs_sub_comm]
      simpa only [one_mul] using mul_le_mul hN hd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h := mul_nonneg he (sub_nonneg.mpr hden)
    nlinarith
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

/-- Original `quaternion_norm_le_l1` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem quaternion_norm_le_l1 (q : ℍ) : ‖q‖ ≤ |q.re|+|q.imI|+|q.imJ|+|q.imK| := by
  have hs : ‖q‖^2=|q.re|^2+|q.imI|^2+|q.imJ|^2+|q.imK|^2 := by
    simp only [sq_abs]
    rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_def']
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [mul_nonneg (abs_nonneg q.re) (abs_nonneg q.imI),
    mul_nonneg (abs_nonneg q.re) (abs_nonneg q.imJ),mul_nonneg (abs_nonneg q.re) (abs_nonneg q.imK),
    mul_nonneg (abs_nonneg q.imI) (abs_nonneg q.imJ),mul_nonneg (abs_nonneg q.imI) (abs_nonneg q.imK),
    mul_nonneg (abs_nonneg q.imJ) (abs_nonneg q.imK)]

/-- Original `unit_transverse_bounds` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
private theorem unit_transverse_bounds (s : ℍ) (hn : ‖s‖=1) : |s.imJ| ≤ 1 ∧ |s.imK| ≤ 1 := by
  have hs := (normSq_eq_one_iff s).mpr hn
  rw [Quaternion.normSq_def'] at hs
  have hj : s.imJ^2 ≤ (1 : ℝ)^2 := by nlinarith [sq_nonneg s.re,sq_nonneg s.imI,sq_nonneg s.imK]
  have hk : s.imK^2 ≤ (1 : ℝ)^2 := by nlinarith [sq_nonneg s.re,sq_nonneg s.imI,sq_nonneg s.imJ]
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [sq_abs] using hj
  · apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [sq_abs] using hk

/-- Fixed-chart seed values have a uniform absolute error without any unit
identity for approximate spin samples. The output itself need not be unit. -/
theorem rationalChartSeed_error (chart : SeedChart) (a : Fin 3 → ℚ) (s : ℍ) (hn : ‖s‖=1)
    (hc : match chart with
      | .north => -(1/2 : ℝ)<s.imI
      | .south => s.imI<(1/2 : ℝ))
    (b : ℕ) (hb : 8 ≤ b)
    (he : ∀ j, |(a j : ℝ)-(![s.imI,s.imJ,s.imK] j)| ≤ (2^b : ℝ)⁻¹) :
    ‖rationalQuaternionCast (rationalChartSeed chart a b)-exactChartSeed chart s‖ ≤ 32*(2^b : ℝ)⁻¹ := by
  let e : ℝ := (2^b : ℝ)⁻¹
  have he0 : 0 ≤ e := by positivity
  obtain ⟨hJ,hK⟩ := unit_transverse_bounds s hn
  cases chart with
  | north =>
    let r := seedSqrtFloor ((1+a 0)/2) b
    let A := Real.sqrt ((1+s.imI)/2)
    let d := rationalQuaternionCast (rationalChartSeed .north a b)-northSeed s
    have hr := seedRoot_error (a 0) s.imI b hb hc (he 0)
    have hA : (1/2 : ℝ) ≤ A := (northSeed_margin s hc).le
    have hj := seedQuotient_error (a 2) r s.imK A e he0 hr.1 hA hK (he 2) hr.2
    have hk := seedQuotient_error (a 1) r s.imJ A e he0 hr.1 hA hJ (he 1) hr.2
    have hre : |d.re| ≤ 2*e := hr.2
    have hi : |d.imI|=0 := by simp [d,rationalQuaternionCast,rationalChartSeed,northSeed]
    have hj' : |d.imJ| ≤ 10*e := by
      change |((a 2/(2*r) : ℚ) : ℝ)-s.imK/(2*A)| ≤ _
      push_cast
      exact hj
    have hk' : |d.imK| ≤ 10*e := by
      have hid : d.imK= -((a 1 : ℝ)/(2*(r : ℝ))-s.imJ/(2*A)) := by
        dsimp [d,rationalQuaternionCast,rationalChartSeed,northSeed,r,A]
        push_cast
        ring
      rw [hid,abs_neg]
      exact hk
    change ‖d‖ ≤ 32*e
    have h := quaternion_norm_le_l1 d
    linarith
  | south =>
    let r := seedSqrtFloor ((1-a 0)/2) b
    let A := Real.sqrt ((1-s.imI)/2)
    let d := rationalQuaternionCast (rationalChartSeed .south a b)-southSeed s
    have hr : (1/4 : ℝ) ≤ (r : ℝ) ∧ |(r : ℝ)-A| ≤ 2*e := by
      have h := seedRoot_error (-a 0) (-s.imI) b hb (by linarith)
        (by simpa only [Matrix.cons_val_zero,Rat.cast_neg,neg_sub_neg,abs_sub_comm] using he 0)
      simpa only [r,A,e,sub_eq_add_neg] using h
    have hA : (1/2 : ℝ) ≤ A := (southSeed_margin s hc).le
    have hre := seedQuotient_error (a 2) r s.imK A e he0 hr.1 hA hK (he 2) hr.2
    have hi := seedQuotient_error (a 1) r s.imJ A e he0 hr.1 hA hJ (he 1) hr.2
    have hre' : |d.re| ≤ 10*e := by
      change |((a 2/(2*r) : ℚ) : ℝ)-s.imK/(2*A)| ≤ _
      push_cast
      exact hre
    have hi' : |d.imI| ≤ 10*e := by
      change |((a 1/(2*r) : ℚ) : ℝ)-s.imJ/(2*A)| ≤ _
      push_cast
      exact hi
    have hj : |d.imJ| ≤ 2*e := hr.2
    have hk : |d.imK|=0 := by simp [d,rationalQuaternionCast,rationalChartSeed,southSeed]
    change ‖d‖ ≤ 32*e
    have h := quaternion_norm_le_l1 d
    linarith

/-- Original `originSeedApproximation_error` guarantee for the `SeedApproximation` construction; the complete source hypotheses are retained. -/
theorem originSeedApproximation_error (v : SpatialPoint → SpatialPoint) (hu : ∀ w, ‖v w‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hsource : OriginalSpinSourceAccurate v source)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ‖rationalQuaternionCast (originSeedApproximation source tolerance)-chosenOriginSeed v source‖ ≤ (tolerance : ℝ) := by
  have hs := originSpinSamples_error v source hsource (seedValuePrecision tolerance)
  have h := rationalChartSeed_error (chosenOriginChart source)
    (originSpinSamples source (seedValuePrecision tolerance)) (sourceQuaternion v 0)
    ((spinOfVector_norm _).trans (hu 0)) (chosenOriginChart_valid v source hsource)
    _ (seedValuePrecision_eight tolerance)
    (by intro j; fin_cases j <;> simpa [sourceQuaternion,spinOfVector] using hs _)
  have hb : ((32*(2^seedValuePrecision tolerance : ℚ)⁻¹ : ℚ) : ℝ) ≤ (tolerance : ℝ) :=
    Rat.cast_le.mpr (seedValuePrecision_budget tolerance ht)
  push_cast at hb
  exact h.trans hb

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
