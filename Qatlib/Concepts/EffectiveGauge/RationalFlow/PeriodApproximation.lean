/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ArctanProgram
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Model
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The actual Machin program and a short dyadic lower period -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of rational Pi in the Rational Flow construction. -/
def rationalPi (tolerance : ℚ) : RationalScalarResult :=
  let a := rationalArctan (1/5) (tolerance/32)
  let b := rationalArctan (1/239) (tolerance/32)
  ⟨16*a.value-4*b.value,16*a.error+4*b.error,a.terms+b.terms⟩

/-- Definition of period Dyadic Floor in the Rational Flow construction. -/
def periodDyadicFloor (a : ℚ) (b : ℕ) : ℚ := (Int.floor (a*(2^b : ℚ)) : ℚ)/(2^b : ℚ)

/-- Definition of period Lower in the Rational Flow construction. -/
def periodLower (b : ℕ) : ℚ :=
  let p := rationalPi ((2^(b+3) : ℚ)⁻¹)
  periodDyadicFloor (2*p.value-2*p.error) (b+2)

/-- Original `periodDyadicFloor_le` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodDyadicFloor_le (a : ℚ) (b : ℕ) : periodDyadicFloor a b ≤ a := by
  unfold periodDyadicFloor
  apply (div_le_iff₀ (by positivity : (0 : ℚ)<2^b)).mpr
  exact Int.floor_le _

/-- Original `periodDyadicFloor_gap` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodDyadicFloor_gap (a : ℚ) (b : ℕ) : a-periodDyadicFloor a b ≤ (2^b : ℚ)⁻¹ := by
  have hp : (0 : ℚ)<2^b := by positivity
  have h := Int.lt_floor_add_one (a*(2^b : ℚ))
  have he : a-periodDyadicFloor a b=(a*(2^b : ℚ)-(Int.floor (a*(2^b : ℚ)) : ℚ))/(2^b : ℚ) := by
    dsimp [periodDyadicFloor]
    field_simp
    rfl
  rw [he]
  apply (div_le_iff₀ hp).mpr
  have hi : (2^b : ℚ)⁻¹*(2^b : ℚ)=1 := inv_mul_cancel₀ hp.ne'
  rw [hi]
  linarith

/-- Original `periodLower_encoding` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodLower_encoding (b : ℕ) : ∃ n : ℤ, periodLower b=(n : ℚ)/(2^(b+2) : ℚ) :=
  ⟨_,rfl⟩

noncomputable section

/-- Original `rationalPi_error` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem rationalPi_error (tolerance : ℚ) (ht : 0<tolerance) :
    |((rationalPi tolerance).value : ℝ)-Real.pi| ≤ ((rationalPi tolerance).error : ℝ) ∧
      0 ≤ (rationalPi tolerance).error ∧ (rationalPi tolerance).error ≤ tolerance ∧
      (rationalPi tolerance).terms ≤ 2*arctanFuel (tolerance/32) := by
  let a := rationalArctan (1/5) (tolerance/32)
  let b := rationalArctan (1/239) (tolerance/32)
  have ha := rationalArctan_error (1/5) (tolerance/32) (by norm_num) (by positivity)
  have hb := rationalArctan_error (1/239) (tolerance/32) (by norm_num) (by positivity)
  push_cast at ha hb
  have hsa := rationalArctan_spec (1/5) (tolerance/32) (by norm_num) (by positivity)
  have hsb := rationalArctan_spec (1/239) (tolerance/32) (by norm_num) (by positivity)
  have han : (0 : ℚ) ≤ a.error := Rat.cast_nonneg.mp ((abs_nonneg _).trans ha)
  have hbn : (0 : ℚ) ≤ b.error := Rat.cast_nonneg.mp ((abs_nonneg _).trans hb)
  have hm : 4*Real.arctan (1/5)-Real.arctan (1/239)=Real.pi/4 := by
    simpa only [one_div] using Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have he : |((rationalPi tolerance).value : ℝ)-Real.pi| ≤ ((rationalPi tolerance).error : ℝ) := by
    have hid : ((rationalPi tolerance).value : ℝ)-Real.pi=
        16*((a.value : ℝ)-Real.arctan (1/5))-4*((b.value : ℝ)-Real.arctan (1/239)) := by
      dsimp [rationalPi,a,b]
      push_cast
      linarith
    rw [hid]
    calc
      _ ≤ |16*((a.value : ℝ)-Real.arctan (1/5))|+|4*((b.value : ℝ)-Real.arctan (1/239))| := abs_sub _ _
      _ = 16*|(a.value : ℝ)-Real.arctan (1/5)|+4*|(b.value : ℝ)-Real.arctan (1/239)| := by
        rw [abs_mul,abs_mul]
        norm_num
      _ ≤ 16*(a.error : ℝ)+4*(b.error : ℝ) := add_le_add
        (mul_le_mul_of_nonneg_left ha (by norm_num)) (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = _ := by simp [rationalPi,a,b]
  refine ⟨he,by change 0 ≤ 16*a.error+4*b.error; positivity,?_,?_⟩
  · change 16*a.error+4*b.error ≤ tolerance
    have ha' : a.error ≤ tolerance/32 := hsa.2.2.2.1
    have hb' : b.error ≤ tolerance/32 := hsb.2.2.2.1
    linarith
  · change a.terms+b.terms ≤ 2*arctanFuel (tolerance/32)
    have ha' : a.terms ≤ arctanFuel (tolerance/32) := hsa.2.2.1
    have hb' : b.terms ≤ arctanFuel (tolerance/32) := hsb.2.2.1
    omega

/-- Original `periodLower_enclosure` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodLower_enclosure (b : ℕ) :
    (periodLower b : ℝ) ≤ physicalPeriod ∧
      physicalPeriod-(periodLower b : ℝ) ≤ 3*(2^(b+2) : ℝ)⁻¹ := by
  let p := rationalPi ((2^(b+3) : ℚ)⁻¹)
  have hp := rationalPi_error ((2^(b+3) : ℚ)⁻¹) (by positivity)
  have hpi : |(p.value : ℝ)-Real.pi| ≤ (p.error : ℝ) := hp.1
  have hloQ : periodLower b ≤ 2*p.value-2*p.error := periodDyadicFloor_le _ _
  have hgapQ : 2*p.value-2*p.error-periodLower b ≤ (2^(b+2) : ℚ)⁻¹ := periodDyadicFloor_gap _ _
  have hlo : (periodLower b : ℝ) ≤ 2*(p.value : ℝ)-2*(p.error : ℝ) := by
    have h : (periodLower b : ℝ) ≤ ((2*p.value-2*p.error : ℚ) : ℝ) := Rat.cast_le.mpr hloQ
    push_cast at h
    exact h
  have hgap : 2*(p.value : ℝ)-2*(p.error : ℝ)-(periodLower b : ℝ) ≤ (2^(b+2) : ℝ)⁻¹ := by
    have h : ((2*p.value-2*p.error-periodLower b : ℚ) : ℝ) ≤ (((2^(b+2) : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_le.mpr hgapQ
    push_cast at h
    exact h
  have he : (p.error : ℝ) ≤ (2^(b+3) : ℝ)⁻¹ := by
    have h : (p.error : ℝ) ≤ (((2^(b+3) : ℚ)⁻¹ : ℚ) : ℝ) := Rat.cast_le.mpr hp.2.2.1
    push_cast at h
    exact h
  have hdy : (2^(b+3) : ℝ)⁻¹=(2^(b+2) : ℝ)⁻¹/2 := by
    rw [show b+3=(b+2)+1 by omega,pow_succ,mul_inv_rev]
    ring
  rw [hdy] at he
  have hbounds := abs_le.mp hpi
  dsimp only [physicalPeriod]
  constructor <;> linarith

/-- Original `periodLower_zero` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodLower_zero : periodLower 0=25/4 := by decide +kernel
/-- Original `periodLower_one` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodLower_one : periodLower 1=25/4 := by decide +kernel

/-- All parameters are physical: the lower endpoint is positive and remains
inside [0,2π], its error is dyadic, and its code has denominator 2^(b+2). -/
theorem periodLower_spec (b : ℕ) :
    6<(periodLower b : ℝ) ∧ (periodLower b : ℝ) ≤ physicalPeriod ∧
      physicalPeriod-(periodLower b : ℝ) ≤ (2^b : ℝ)⁻¹ ∧ (periodLower b : ℝ)<7 := by
  obtain ⟨hle,hwidth⟩ := periodLower_enclosure b
  have hdy : (2^(b+2) : ℝ)⁻¹=(2^b : ℝ)⁻¹/4 := by
    rw [pow_add,show (2 : ℝ)^2=4 by norm_num,mul_inv_rev]
    ring
  have hsmall : physicalPeriod-(periodLower b : ℝ) ≤ (2^b : ℝ)⁻¹ := by
    rw [hdy] at hwidth
    linarith [show (0 : ℝ) ≤ (2^b : ℝ)⁻¹ by positivity]
  have hlower : 6<(periodLower b : ℝ) := by
    by_cases h0 : b=0
    · subst b
      rw [periodLower_zero]
      norm_num
    by_cases h1 : b=1
    · subst b
      rw [periodLower_one]
      norm_num
    have hb : 4 ≤ b+2 := by omega
    have hpow : (16 : ℝ) ≤ 2^(b+2) := by exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hb
    have hh : (2^(b+2) : ℝ)⁻¹ ≤ (1/16 : ℝ) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<16) hpow
    have hpi : (6.28 : ℝ)<physicalPeriod := by dsimp [physicalPeriod]; linarith [Real.pi_gt_d2]
    linarith
  have hupper : physicalPeriod<(7 : ℝ) := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  exact ⟨hlower,hle,hsmall,hle.trans_lt hupper⟩

/-- Original `periodMachin_terms` guarantee for the `PeriodApproximation` construction; the complete source hypotheses are retained. -/
theorem periodMachin_terms (b : ℕ) :
    (rationalPi ((2^(b+3) : ℚ)⁻¹)).terms ≤ 2*(b+8) := by
  have ht : (0 : ℚ)<(2^(b+3) : ℚ)⁻¹ := by positivity
  have h := (rationalPi_error ((2^(b+3) : ℚ)⁻¹) ht).2.2.2
  have he : ((2^(b+3) : ℚ)⁻¹)/32=(2^(b+8) : ℚ)⁻¹ := by
    have hp : (2^(b+8) : ℚ)=(2^(b+3) : ℚ)*32 := by
      rw [show b+8=(b+3)+5 by omega,pow_add]
      norm_num
    rw [hp,mul_inv_rev]
    ring
  rw [he,arctanFuel_inverse_power_two] at h
  exact h

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
