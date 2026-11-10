/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.Tulsi
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

def phase (α : ℝ) : ℂ := (Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I

theorem phase_neg (α : ℝ) : phase (-α) = starRingEnd ℂ (phase α) := by
  apply Complex.ext
  · simp [phase, Real.cos_neg]
  · simp [phase, Real.cos_neg, Real.sin_neg]

theorem cot_neg (x : ℝ) : cot (-x) = -cot x := by
  simp [cot, Real.cos_neg, Real.sin_neg, div_neg]

theorem cot_pos_of_pos_of_lt_half_pi {x : ℝ} (h0 : 0 < x) (h1 : x < Real.pi / 2) :
    0 < cot x := by
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  exact div_pos hcos hsin

theorem overlap_paired (P : Type*) [Fintype P] (W α : P → ℝ) (c : ℝ)
    (hW : ∀ p, W p ≠ 0) :
    (∑ a : P × Bool,
        (1 / (W a.1 : ℂ)) *
          (if a.2 then phase (α a.1) else phase (-α a.1)) *
          (Complex.I * (c : ℂ) *
            (cot ((if a.2 then α a.1 else -α a.1) / 2) : ℂ) / (W a.1 : ℂ)) *
        (W a.1 : ℂ))
      = (-2 : ℂ) * (c : ℂ) *
          ∑ p, (Real.sin (α p) : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ) := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ p : P,
      (∑ b : Bool,
        (1 / (W p : ℂ)) *
          (if b then phase (α p) else phase (-α p)) *
          (Complex.I * (c : ℂ) *
            (cot ((if b then α p else -α p) / 2) : ℂ) / (W p : ℂ)) *
        (W p : ℂ))
      = (-2 : ℂ) * (c : ℂ) * ((Real.sin (α p) : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ)) := by
    intro p
    have hWp : (W p : ℂ) ≠ 0 := by simpa using hW p
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, if_true, if_false]
    rw [show -α p / 2 = -(α p / 2) by ring, cot_neg]
    have hphase : phase (α p) - phase (-α p) = 2 * Complex.I * (Real.sin (α p) : ℂ) := by
      apply Complex.ext
      · simp [phase]
      · simp [phase, Real.sin_neg]
        ring
    have h1 : (1 / (W p : ℂ)) * phase (α p) *
          (Complex.I * (c : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ)) * (W p : ℂ)
        = Complex.I * (c : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ) * phase (α p) := by
      field_simp
    have h2 : (1 / (W p : ℂ)) * phase (-α p) *
          (Complex.I * (c : ℂ) * (((-cot (α p / 2) : ℝ)) : ℂ) / (W p : ℂ)) * (W p : ℂ)
        = -(Complex.I * (c : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ)) * phase (-α p) := by
      field_simp
      simp only [Complex.ofReal_neg]
      ring
    rw [h1, h2]
    have hsplit : Complex.I * (c : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ) * phase (α p) +
          -(Complex.I * (c : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ)) * phase (-α p)
        = Complex.I * (c : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ) *
            (phase (α p) - phase (-α p)) := by ring
    rw [hsplit, hphase]
    have hII : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
    field_simp
    ring_nf
    simp only [hII, pow_two]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hinner p)]
  rw [← Finset.mul_sum]

end Qatlib.Papers.HittingTimes08.MainResults

namespace Qatlib.Papers.HittingTimes08.MainResults

theorem lemma_4_2 (P : Type*) [Fintype P] (W α : P → ℝ) (a0 : ℝ)
    (hW : ∀ p, W p ≠ 0) :
    (∑ a : P × Bool,
        (1 / (W a.1 : ℂ)) *
          (if a.2 then phase (α a.1) else phase (-α a.1)) *
          (Complex.I * (a0 : ℂ) *
            (cot ((if a.2 then α a.1 else -α a.1) / 2) : ℂ) / (W a.1 : ℂ)) *
        (W a.1 : ℂ))
      = (-2 : ℂ) * (a0 : ℂ) *
          ∑ p, (Real.sin (α p) : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ) :=
  overlap_paired P W α a0 hW

theorem corollary_4_6 (P : Type*) [Fintype P] (W α : P → ℝ) (a0 θ : ℝ)
    (hW : ∀ p, W p ≠ 0) :
    (∑ a : P × Bool,
        (1 / (W a.1 : ℂ)) *
          (if a.2 then phase (α a.1) else phase (-α a.1)) *
          (Complex.I * ((a0 * Real.cos θ) : ℂ) *
            (cot ((if a.2 then α a.1 else -α a.1) / 2) : ℂ) / (W a.1 : ℂ)) *
        (W a.1 : ℂ))
      = (-2 : ℂ) * ((a0 * Real.cos θ) : ℂ) *
          ∑ p, (Real.sin (α p) : ℂ) * (cot (α p / 2) : ℂ) / (W p : ℂ) := by
  simpa only [Complex.ofReal_mul] using overlap_paired P W α (a0 * Real.cos θ) hW

theorem lemma_4_4_equation {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θ : ℝ) (θj : J → ℝ) (x : ℝ) (hcos : Real.cos θ ≠ 0)
    (h : (a0 * Real.cos θ) ^ 2 * cot (x / 2) +
          (∑ j, (a j * Real.cos θ) ^ 2 *
            (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
          (Real.sin θ) ^ 2 * Real.tan (x / 2) = 0) :
    a0 ^ 2 * cot (x / 2) +
        (∑ j, a j ^ 2 *
          (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
        Real.tan θ ^ 2 * Real.tan (x / 2) = 0 := by
  have hcos2 : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have hsum : Real.cos θ ^ 2 *
        (∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)))
      = ∑ j, (a j * Real.cos θ) ^ 2 *
          (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hkey : Real.cos θ ^ 2 *
        (a0 ^ 2 * cot (x / 2) +
          (∑ j, a j ^ 2 *
            (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
          Real.tan θ ^ 2 * Real.tan (x / 2))
      = (a0 * Real.cos θ) ^ 2 * cot (x / 2) +
          (∑ j, (a j * Real.cos θ) ^ 2 *
            (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
          (Real.sin θ) ^ 2 * Real.tan (x / 2) := by
    rw [show Real.tan θ = Real.sin θ / Real.cos θ from Real.tan_eq_sin_div_cos θ,
      mul_sub, mul_add, hsum]
    field_simp
  have hmul : Real.cos θ ^ 2 *
      (a0 ^ 2 * cot (x / 2) +
        (∑ j, a j ^ 2 *
          (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
        Real.tan θ ^ 2 * Real.tan (x / 2)) = 0 := by
    rw [hkey]; exact h
  exact (mul_eq_zero.mp hmul).resolve_left hcos2

theorem cot_eq_one_div_tan (x : ℝ) : cot x = 1 / Real.tan x := by
  rw [cot, Real.tan_eq_sin_div_cos, one_div_div]

theorem cot_lt_cot {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < Real.pi / 2) :
    cot y < cot x := by
  have htan : Real.tan x < Real.tan y :=
    Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos]) hy hxy
  have hpx : 0 < Real.tan x := Real.tan_pos_of_pos_of_lt_pi_div_two hx (by linarith)
  have hsx : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos]))
  have hsy : Real.sin y ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  rw [cot_eq_one_div_tan x, cot_eq_one_div_tan y]
  exact one_div_lt_one_div_of_lt hpx htan

theorem tan_sub_tan (u v : ℝ) (hu : Real.cos u ≠ 0) (hv : Real.cos v ≠ 0) :
    Real.tan u - Real.tan v = Real.sin (u - v) / (Real.cos u * Real.cos v) := by
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub]
  field_simp

theorem tan_ratio_lower {a : ℝ} (h0 : 0 < a) (ha : a ≤ Real.pi / 4) :
    (101 / 100 : ℝ) * Real.tan (39 / 100 * a) ≤ Real.tan (a / 2) := by
  have hpi := Real.pi_pos
  have hv0 : 0 ≤ 39 / 100 * a := by positivity
  have hv_lt : 39 / 100 * a < Real.pi / 2 := by nlinarith [hpi]
  have hu_lt : a / 2 < Real.pi / 2 := by nlinarith [hpi]
  have hcu : 0 < Real.cos (a / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi], hu_lt⟩
  have hcv : 0 < Real.cos (39 / 100 * a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi], hv_lt⟩
  have hsub := tan_sub_tan (a / 2) (39 / 100 * a) (ne_of_gt hcu) (ne_of_gt hcv)
  have harg : a / 2 - 39 / 100 * a = 11 / 100 * a := by ring
  rw [harg] at hsub
  have hsin_low : (2 / Real.pi) * (11 / 100 * a) ≤ Real.sin (11 / 100 * a) :=
    Real.mul_le_sin (by positivity) (by nlinarith [hpi])
  have hsin_up : Real.sin (39 / 100 * a) ≤ 39 / 100 * a := Real.sin_le hv0
  have hpi2 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ hpi]
    nlinarith [Real.pi_lt_four]
  have hsin_nonneg : 0 ≤ Real.sin (11 / 100 * a) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    nlinarith [hpi]

  have hLHS : 11 / 200 * a ≤ Real.sin (11 / 100 * a) / Real.cos (a / 2) := by
    have hsin_ge : 11 / 200 * a ≤ Real.sin (11 / 100 * a) := by
      nlinarith [hsin_low, hpi2, h0]
    have hcu_le : Real.cos (a / 2) ≤ 1 := Real.cos_le_one _
    calc 11 / 200 * a ≤ Real.sin (11 / 100 * a) := hsin_ge
      _ = Real.sin (11 / 100 * a) / 1 := by ring
      _ ≤ Real.sin (11 / 100 * a) / Real.cos (a / 2) := by
            exact div_le_div_of_nonneg_left hsin_nonneg hcu hcu_le

  have hRHS : (1 / 100) * Real.sin (39 / 100 * a) ≤ 11 / 200 * a := by
    have h1 : (1 / 100) * Real.sin (39 / 100 * a) ≤ (1 / 100) * (39 / 100 * a) := by
      exact mul_le_mul_of_nonneg_left hsin_up (by norm_num)
    nlinarith [h1, h0]
  have hmain : (1 / 100) * Real.sin (39 / 100 * a) ≤
      Real.sin (11 / 100 * a) / Real.cos (a / 2) := le_trans hRHS hLHS

  have hinvpos : 0 < 1 / Real.cos (39 / 100 * a) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmain hinvpos.le
  have htanv : (1 / 100) * Real.tan (39 / 100 * a) ≤
      Real.sin (11 / 100 * a) / (Real.cos (a / 2) * Real.cos (39 / 100 * a)) := by
    calc (1 / 100) * Real.tan (39 / 100 * a)
        = ((1 / 100) * Real.sin (39 / 100 * a)) * (1 / Real.cos (39 / 100 * a)) := by
          rw [Real.tan_eq_sin_div_cos]; ring
      _ ≤ (Real.sin (11 / 100 * a) / Real.cos (a / 2)) *
            (1 / Real.cos (39 / 100 * a)) := hmul
      _ = Real.sin (11 / 100 * a) / (Real.cos (a / 2) * Real.cos (39 / 100 * a)) := by ring

  have hpos_u : 0 < Real.tan (a / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [hpi])
  have : (1 / 100) * Real.tan (39 / 100 * a) ≤ Real.tan (a / 2) - Real.tan (39 / 100 * a) := by
    rw [hsub]; exact htanv
  linarith

theorem lemma_4_7_alpha_lower {a x : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 4)
    (hx0 : 0 < x)
    (hcot : cot (x / 2) ≤ (101 / 100) * cot (a / 2)) :
    (78 / 100) * a ≤ x := by
  by_contra hnot
  have hxlt : x < 78 / 100 * a := by linarith
  have hxhalf : x / 2 < 39 / 100 * a := by linarith
  have hmono : cot (39 / 100 * a) < cot (x / 2) :=
    cot_lt_cot (by linarith : 0 < x / 2) hxhalf (by nlinarith [Real.pi_pos, ha])
  have htan := tan_ratio_lower ha0 ha
  have hpos_u : 0 < Real.tan (a / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
  have hpos_v : 0 < Real.tan (39 / 100 * a) := by
    apply Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity)
    nlinarith [Real.pi_pos]
  have hbase : (101 / 100) * cot (a / 2) ≤ cot (39 / 100 * a) := by
    rw [cot_eq_one_div_tan (a / 2),
      cot_eq_one_div_tan (39 / 100 * a)]
    rw [show (101 / 100) * (1 / Real.tan (a / 2)) = (101 / 100) / Real.tan (a / 2) by ring,
      div_le_div_iff₀ hpos_u hpos_v]
    nlinarith [htan]
  linarith [hbase, hmono, hcot]

theorem cot_lt_cot_of_pos_of_lt_pi {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < Real.pi) : cot y < cot x := by
  have hpi := Real.pi_pos
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi (by linarith) hy
  have hsx' : Real.sin x ≠ 0 := ne_of_gt hsx
  have hsy' : Real.sin y ≠ 0 := ne_of_gt hsy
  have hsin : Real.sin (x - y) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hkey : cot y - cot x = Real.sin (x - y) / (Real.sin y * Real.sin x) := by
    rw [cot, cot, Real.sin_sub]
    field_simp [hsx', hsy']
  have hneg : cot y - cot x < 0 := by
    rw [hkey]
    exact div_neg_of_neg_of_pos hsin (mul_pos hsy hsx)
  linarith

theorem cot_lt_cot_of_neg_of_neg_pi_lt {x y : ℝ} (hx : -Real.pi < x) (hxy : x < y)
    (hy : y < 0) : cot y < cot x := by
  have h1 : cot y = -cot (-y) := by
    rw [cot_neg]
    ring
  have h2 : cot x = -cot (-x) := by
    rw [cot_neg]
    ring
  rw [h1, h2]
  have hlt : cot (-x) < cot (-y) :=
    cot_lt_cot_of_pos_of_lt_pi (by linarith) (by linarith) (by linarith)
  linarith

theorem cot_le_cot_of_pos_of_le_of_lt_pi {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y < Real.pi) : cot y ≤ cot x := by
  rcases lt_or_eq_of_le hxy with h | h
  · exact (cot_lt_cot_of_pos_of_lt_pi hx h hy).le
  · rw [h]

theorem cot_le_cot_of_neg_of_le_of_neg_pi_lt {x y : ℝ} (hx : -Real.pi < x)
    (hxy : x ≤ y) (hy : y < 0) : cot y ≤ cot x := by
  rcases lt_or_eq_of_le hxy with h | h
  · exact (cot_lt_cot_of_neg_of_neg_pi_lt hx h hy).le
  · rw [h]

theorem cot_le_pi_div_two_mul {t : ℝ} (h0 : 0 < t) (ht : t ≤ Real.pi / 2) :
    cot t ≤ Real.pi / (2 * t) := by
  have hpi := Real.pi_pos
  have hsin_pos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsin_low : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin h0.le ht
  have h1 : cot t ≤ 1 / Real.sin t := by
    rw [cot]
    exact div_le_div_of_nonneg_right (Real.cos_le_one t) hsin_pos.le
  have h2 : 1 / Real.sin t ≤ 1 / (2 / Real.pi * t) :=
    one_div_le_one_div_of_le (by positivity) hsin_low
  have h3 : 1 / (2 / Real.pi * t) = Real.pi / (2 * t) := by
    field_simp [Real.pi_ne_zero, ne_of_gt h0]
  linarith [h1, h2, h3]

theorem cot_ge_one_div_sub {t : ℝ} (h0 : 0 < t) (ht : t ≤ Real.pi / 4) :
    1 / t - t / 2 ≤ cot t := by
  have hpi := Real.pi_pos
  have hsin_pos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsin_le : Real.sin t ≤ t := Real.sin_le h0.le
  have hcos_ge : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  have hnum : 0 ≤ 1 - t ^ 2 / 2 := by
    have ht2 : t ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith [h0.le, ht]
    have hpi4 : (Real.pi / 4) ^ 2 ≤ 1 := by nlinarith [Real.pi_lt_four, hpi]
    nlinarith
  have hstep1 : (1 - t ^ 2 / 2) / t ≤ (1 - t ^ 2 / 2) / Real.sin t :=
    div_le_div_of_nonneg_left hnum hsin_pos hsin_le
  have hstep2 : (1 - t ^ 2 / 2) / Real.sin t ≤ Real.cos t / Real.sin t :=
    div_le_div_of_nonneg_right hcos_ge hsin_pos.le
  have heq : (1 - t ^ 2 / 2) / t = 1 / t - t / 2 := by
    field_simp [ne_of_gt h0]
  rw [cot, ← heq]
  linarith [hstep1, hstep2]

theorem tan_le_two_mul {t : ℝ} (h0 : 0 < t) (ht : t ≤ Real.pi / 4) :
    Real.tan t ≤ 2 * t := by
  have hpi := Real.pi_pos
  have hcos_ge : 1 / 2 ≤ Real.cos t := by
    have h := Real.one_sub_sq_div_two_le_cos (x := t)
    have ht2 : t ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith [h0.le, ht]
    have hpi4 : (Real.pi / 4) ^ 2 ≤ 1 := by nlinarith [Real.pi_lt_four, hpi]
    nlinarith
  have hcos_pos : 0 < Real.cos t := by linarith
  have hsin_le : Real.sin t ≤ t := Real.sin_le h0.le
  rw [Real.tan_eq_sin_div_cos]
  have h1 : Real.sin t / Real.cos t ≤ t / Real.cos t :=
    div_le_div_of_nonneg_right hsin_le hcos_pos.le
  have h2 : t / Real.cos t ≤ t / (1 / 2) :=
    div_le_div_of_nonneg_left h0.le (by norm_num) hcos_ge
  have h3 : t / (1 / 2) = 2 * t := by ring
  linarith [h1, h2, h3]

theorem continuousOn_cot_comp {c : ℝ} {s : Set ℝ}
    (h : ∀ x ∈ s, Real.sin ((x + c) / 2) ≠ 0) :
    ContinuousOn (fun x => cot ((x + c) / 2)) s := by
  have hcont : Continuous fun x : ℝ => (x + c) / 2 := by continuity
  have hsin : ContinuousOn (fun x : ℝ => Real.sin ((x + c) / 2)) s :=
    Real.continuous_sin.continuousOn.comp hcont.continuousOn (fun x _ => Set.mem_univ _)
  have hcos : ContinuousOn (fun x : ℝ => Real.cos ((x + c) / 2)) s :=
    Real.continuous_cos.continuousOn.comp hcont.continuousOn (fun x _ => Set.mem_univ _)
  have hdiv := hcos.div hsin h
  simpa [cot] using! hdiv

def tulsiF {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ) (θj : J → ℝ) (θ x : ℝ) : ℝ :=
  a0 ^ 2 * cot (x / 2) +
    (∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
    Real.tan θ ^ 2 * Real.tan (x / 2)

theorem tulsiF_continuousOn {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ : ℝ) {α : ℝ}
    (hα0 : 0 < α) (hα4 : α ≤ Real.pi / 4)
    (hθ0 : ∀ j, 0 ≤ θj j) (hθ2 : ∀ j, θj j ≤ Real.pi / 2) (hθα : ∀ j, α < θj j)
    (hcosθ : Real.cos θ ≠ 0) :
    ContinuousOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α) := by
  have hpi := Real.pi_pos
  have hx0 : ∀ x ∈ Set.Icc (α / 4) α, 0 < x := by
    intro x hx
    linarith [hx.1, hα0]
  have hterm0 : ContinuousOn (fun x => a0 ^ 2 * cot (x / 2)) (Set.Icc (α / 4) α) := by
    have hcot0 : ContinuousOn (fun x => cot (x / 2)) (Set.Icc (α / 4) α) := by
      have h := continuousOn_cot_comp (c := 0) (s := Set.Icc (α / 4) α) (by
        intro x hx
        have h1 : 0 < (x + 0) / 2 := by linarith [hx0 x hx]
        have h2 : (x + 0) / 2 < Real.pi := by linarith [hx.2, hα4, hpi]
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
      simpa using h
    exact continuousOn_const.mul hcot0
  have htermj : ∀ j : J, ContinuousOn
      (fun x => a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)))
      (Set.Icc (α / 4) α) := by
    intro j
    have hp : ContinuousOn (fun x => cot ((x + θj j) / 2)) (Set.Icc (α / 4) α) :=
      continuousOn_cot_comp (c := θj j) (by
        intro x hx
        have h1 : 0 < (x + θj j) / 2 := by linarith [hx0 x hx, hθ0 j]
        have h2 : (x + θj j) / 2 < Real.pi := by nlinarith [hx.2, hα4, hθ2 j, hpi]
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
    have hm : ContinuousOn (fun x => cot ((x - θj j) / 2)) (Set.Icc (α / 4) α) := by
      have h := continuousOn_cot_comp (c := -θj j) (s := Set.Icc (α / 4) α) (by
        intro x hx
        have h1 : (x + -θj j) / 2 < 0 := by linarith [hx.2, hα4, hθα j]
        have h2 : -Real.pi < (x + -θj j) / 2 := by nlinarith [hx.1, hα0, hθ2 j, hpi]
        exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt h1 h2))
      simpa using! h
    exact continuousOn_const.mul (hp.add hm)
  have hsum : ContinuousOn
      (fun x => ∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)))
      (Set.Icc (α / 4) α) := by
    have h := continuousOn_finsetSum (Finset.univ) (fun j _ => htermj j)
    simpa using h
  have htan : ContinuousOn (fun x => Real.tan θ ^ 2 * Real.tan (x / 2))
      (Set.Icc (α / 4) α) := by
    have hcomp : ContinuousOn (fun x => Real.tan (x / 2)) (Set.Icc (α / 4) α) := by
      have hc : ContinuousOn (fun x : ℝ => x / 2) (Set.Icc (α / 4) α) :=
        (continuous_id.div_const 2).continuousOn
      have h := Real.continuousOn_tan_Ioo.comp hc (fun x hx => by
        constructor
        · linarith [hx0 x hx, hpi]
        · nlinarith [hx.2, hα4, hpi])
      simpa [Function.comp_def] using h
    exact continuousOn_const.mul hcomp
  have h := (hterm0.add hsum).sub htan
  simpa [tulsiF] using! h

theorem tulsiF_strictAntiOn {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ : ℝ) {α : ℝ}
    (ha0 : a0 ≠ 0) (hα0 : 0 < α) (hα4 : α ≤ Real.pi / 4)
    (hθ0 : ∀ j, 0 ≤ θj j) (hθ2 : ∀ j, θj j ≤ Real.pi / 2) (hθα : ∀ j, α < θj j) :
    StrictAntiOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α) := by
  have hpi := Real.pi_pos
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1, hα0]
  have hy4 : y ≤ Real.pi / 4 := le_trans hy.2 hα4
  have hcot0 : cot (y / 2) < cot (x / 2) :=
    cot_lt_cot_of_pos_of_lt_pi (by linarith) (by linarith) (by nlinarith [hy4, hpi])
  have hcotj : ∀ j, cot ((y + θj j) / 2) < cot ((x + θj j) / 2) := by
    intro j
    exact cot_lt_cot_of_pos_of_lt_pi (by linarith [hx0, hθ0 j]) (by linarith)
      (by nlinarith [hy4, hθ2 j, hpi])
  have hcotj' : ∀ j, cot ((y - θj j) / 2) < cot ((x - θj j) / 2) := by
    intro j
    exact cot_lt_cot_of_neg_of_neg_pi_lt (by nlinarith [hx.1, hα0, hθ2 j, hpi])
      (by linarith) (by linarith [hy.2, hα4, hθα j])
  have hA : a0 ^ 2 * cot (y / 2) < a0 ^ 2 * cot (x / 2) :=
    mul_lt_mul_of_pos_left hcot0 (sq_pos_of_ne_zero ha0)
  have hB : (∑ j, a j ^ 2 * (cot ((y + θj j) / 2) + cot ((y - θj j) / 2))) ≤
      ∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [hcotj j, hcotj' j]
  have htanxy : Real.tan (x / 2) < Real.tan (y / 2) :=
    Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [hx0, hpi])
      (by nlinarith [hy4, hpi]) (by linarith)
  have hC : Real.tan θ ^ 2 * Real.tan (x / 2) ≤ Real.tan θ ^ 2 * Real.tan (y / 2) :=
    mul_le_mul_of_nonneg_left htanxy.le (sq_nonneg _)
  unfold tulsiF
  linarith [hA, hB, hC]

theorem tulsiF_root_exists {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ : ℝ) {α : ℝ} (hα0 : 0 < α)
    (hcont : ContinuousOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α))
    (hleft : 0 < tulsiF a0 a θj θ (α / 4))
    (hright : tulsiF a0 a θj θ α ≤ 0) :
    ∃ x ∈ Set.Icc (α / 4) α, tulsiF a0 a θj θ x = 0 := by
  have hab : α / 4 ≤ α := by linarith
  have hmem : (0 : ℝ) ∈ Set.Icc (tulsiF a0 a θj θ α) (tulsiF a0 a θj θ (α / 4)) :=
    ⟨hright, hleft.le⟩
  rcases intermediate_value_Icc' hab hcont hmem with ⟨x, hx, hfx⟩
  exact ⟨x, hx, hfx⟩

theorem tulsiF_root_unique {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ : ℝ) {α : ℝ}
    (hanti : StrictAntiOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α))
    {x y : ℝ} (hx : x ∈ Set.Icc (α / 4) α) (hy : y ∈ Set.Icc (α / 4) α)
    (hfx : tulsiF a0 a θj θ x = 0) (hfy : tulsiF a0 a θj θ y = 0) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h := hanti hx hy hlt
    rw [hfx, hfy] at h
    exact lt_irrefl (0 : ℝ) h
  · have h := hanti hy hx hlt
    rw [hfx, hfy] at h
    exact lt_irrefl (0 : ℝ) h

theorem tulsiF_root_exists_unique {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ : ℝ) {α : ℝ} (hα0 : 0 < α)
    (hcont : ContinuousOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α))
    (hanti : StrictAntiOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α))
    (hleft : 0 < tulsiF a0 a θj θ (α / 4))
    (hright : tulsiF a0 a θj θ α ≤ 0) :
    ∃! x, x ∈ Set.Icc (α / 4) α ∧ tulsiF a0 a θj θ x = 0 := by
  obtain ⟨x, hx, hfx⟩ := tulsiF_root_exists a0 a θj θ hα0 hcont hleft hright
  refine ⟨x, ⟨hx, hfx⟩, ?_⟩
  intro y hy
  exact (tulsiF_root_unique a0 a θj θ hanti hx hy.1 hfx hy.2).symm

theorem lemma_4_7_cot_bound {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ x α : ℝ)
    (ha0 : a0 ≠ 0) (hα0 : 0 < α) (hα4 : α ≤ Real.pi / 4)
    (hθ0 : ∀ j, 0 ≤ θj j) (hθ2 : ∀ j, θj j ≤ Real.pi / 2) (hθα : ∀ j, α < θj j)
    (hx : x ∈ Set.Icc (α / 4) α)
    (hEq8 : a0 ^ 2 * cot (α / 2) +
        (∑ j, a j ^ 2 * (cot ((α + θj j) / 2) + cot ((α - θj j) / 2))) = 0)
    (hroot : tulsiF a0 a θj θ x = 0)
    (htan : Real.tan θ ^ 2 * Real.tan (α / 2) ≤ (1 / 100) * (a0 ^ 2 * cot (α / 2))) :
    cot (x / 2) ≤ (101 / 100) * cot (α / 2) := by
  have hpi := Real.pi_pos
  have hx0 : 0 < x := by linarith [hx.1, hα0]
  have hcot2pos : 0 < cot (α / 2) :=
    cot_pos_of_pos_of_lt_half_pi (by linarith) (by nlinarith [hα4, hpi])
  have hsum_le : (∑ j, a j ^ 2 * (cot ((α + θj j) / 2) + cot ((α - θj j) / 2))) ≤
      ∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hp : cot ((α + θj j) / 2) ≤ cot ((x + θj j) / 2) :=
      cot_le_cot_of_pos_of_le_of_lt_pi (x := (x + θj j) / 2) (y := (α + θj j) / 2)
        (by linarith [hx0, hθ0 j]) (by linarith [hx.2])
        (by nlinarith [hα4, hθ2 j, hpi])
    have hm : cot ((α - θj j) / 2) ≤ cot ((x - θj j) / 2) :=
      cot_le_cot_of_neg_of_le_of_neg_pi_lt (x := (x - θj j) / 2) (y := (α - θj j) / 2)
        (by nlinarith [hx.1, hα0, hθ2 j, hpi]) (by linarith [hx.2])
        (by linarith [hθα j])
    linarith
  have hsumα : (∑ j, a j ^ 2 * (cot ((α + θj j) / 2) + cot ((α - θj j) / 2)))
      = -(a0 ^ 2 * cot (α / 2)) := by linarith [hEq8]
  have hroot' : a0 ^ 2 * cot (x / 2) =
      Real.tan θ ^ 2 * Real.tan (x / 2) -
        (∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) := by
    have hr := hroot
    unfold tulsiF at hr
    linarith
  have htanx : Real.tan (x / 2) ≤ Real.tan (α / 2) := by
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · exact (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [hx0, hpi])
        (by nlinarith [hx.2, hα4, hpi]) (by linarith)).le
    · rw [heq]
  have htanx' : Real.tan θ ^ 2 * Real.tan (x / 2) ≤ Real.tan θ ^ 2 * Real.tan (α / 2) :=
    mul_le_mul_of_nonneg_left htanx (sq_nonneg _)
  have hsumx : -(a0 ^ 2 * cot (α / 2)) ≤
      ∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)) := by
    linarith [hsum_le, hsumα]
  have hstep : a0 ^ 2 * cot (x / 2) ≤
      Real.tan θ ^ 2 * Real.tan (α / 2) + a0 ^ 2 * cot (α / 2) := by
    rw [hroot']
    linarith [htanx', hsumx]
  have ha0sq : 0 < a0 ^ 2 := sq_pos_of_ne_zero ha0
  have hstep' : cot (x / 2) ≤
      (Real.tan θ ^ 2 * Real.tan (α / 2) + a0 ^ 2 * cot (α / 2)) / a0 ^ 2 :=
    (le_div_iff₀ ha0sq).mpr (by linarith [hstep])
  have hbound : (Real.tan θ ^ 2 * Real.tan (α / 2) + a0 ^ 2 * cot (α / 2)) / a0 ^ 2 ≤
      (101 / 100) * cot (α / 2) := by
    rw [div_le_iff₀ ha0sq]
    nlinarith [htan, ha0sq, hcot2pos]
  linarith [hstep', hbound]

theorem lemma_4_7_full {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ : ℝ) {α : ℝ}
    (ha0 : a0 ≠ 0) (hα0 : 0 < α) (hα4 : α ≤ Real.pi / 4)
    (hθ0 : ∀ j, 0 ≤ θj j) (hθ2 : ∀ j, θj j ≤ Real.pi / 2) (hθα : ∀ j, α < θj j)
    (hcont : ContinuousOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α))
    (hanti : StrictAntiOn (tulsiF a0 a θj θ) (Set.Icc (α / 4) α))
    (hleft : 0 < tulsiF a0 a θj θ (α / 4))
    (hright : tulsiF a0 a θj θ α ≤ 0)
    (hEq8 : a0 ^ 2 * cot (α / 2) +
        (∑ j, a j ^ 2 * (cot ((α + θj j) / 2) + cot ((α - θj j) / 2))) = 0)
    (htan : Real.tan θ ^ 2 * Real.tan (α / 2) ≤ (1 / 100) * (a0 ^ 2 * cot (α / 2))) :
    (∃! x, x ∈ Set.Icc (α / 4) α ∧ tulsiF a0 a θj θ x = 0) ∧
      ∀ x, x ∈ Set.Icc (α / 4) α → tulsiF a0 a θj θ x = 0 →
        cot (x / 2) ≤ (101 / 100) * cot (α / 2) ∧ (78 / 100) * α ≤ x := by
  refine ⟨tulsiF_root_exists_unique a0 a θj θ hα0 hcont hanti hleft hright, ?_⟩
  intro x hx hroot
  have hx0 : 0 < x := by linarith [hx.1, hα0]
  refine ⟨lemma_4_7_cot_bound a0 a θj θ x α ha0 hα0 hα4 hθ0 hθ2 hθα hx hEq8 hroot htan,
    ?_⟩
  exact lemma_4_7_alpha_lower hα0 hα4 hx0
    (lemma_4_7_cot_bound a0 a θj θ x α ha0 hα0 hα4 hθ0 hθ2 hθα hx hEq8 hroot htan)

theorem lemma_4_4_coefficients {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ x : ℝ) (hcos : Real.cos θ ≠ 0) :
    (a0 * Real.cos θ) ^ 2 * cot (x / 2) +
        (∑ j, (a j * Real.cos θ) ^ 2 *
          (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
        (Real.sin θ) ^ 2 * Real.tan (x / 2)
      = Real.cos θ ^ 2 *
        (a0 ^ 2 * cot (x / 2) +
          (∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
          Real.tan θ ^ 2 * Real.tan (x / 2)) := by
  have hcos2 : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have hsum : Real.cos θ ^ 2 *
        (∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)))
      = ∑ j, (a j * Real.cos θ) ^ 2 *
          (cot ((x + θj j) / 2) + cot ((x - θj j) / 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [show Real.tan θ = Real.sin θ / Real.cos θ from Real.tan_eq_sin_div_cos θ,
    mul_sub, mul_add, hsum]
  field_simp [hcos]

theorem lemma_4_4_equation_iff {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θj : J → ℝ) (θ x : ℝ) (hcos : Real.cos θ ≠ 0) :
    ((a0 * Real.cos θ) ^ 2 * cot (x / 2) +
        (∑ j, (a j * Real.cos θ) ^ 2 *
          (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
        (Real.sin θ) ^ 2 * Real.tan (x / 2) = 0) ↔
      a0 ^ 2 * cot (x / 2) +
        (∑ j, a j ^ 2 * (cot ((x + θj j) / 2) + cot ((x - θj j) / 2))) -
        Real.tan θ ^ 2 * Real.tan (x / 2) = 0 := by
  constructor
  · exact lemma_4_4_equation a0 a θ θj x hcos
  · intro h
    have hcoe := lemma_4_4_coefficients a0 a θj θ x hcos
    have hcos2 : Real.cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
    rw [hcoe, h, mul_zero]

theorem rotation_overlap_paired (P : Type*) [Fintype P] (W α : P → ℝ) (c : ℝ)
    (hW : ∀ p, W p ≠ 0) :
    (∑ a : P × Bool,
        (1 / (W a.1 : ℂ)) *
          (if a.2 then (1 : ℂ) else -1) *
          (Complex.I * (c : ℂ) *
            (cot ((if a.2 then α a.1 else -α a.1) / 2) : ℂ) / (W a.1 : ℂ)) *
        (W a.1 : ℂ))
      = 2 * Complex.I * (c : ℂ) * ∑ p, (cot (α p / 2) : ℂ) / (W p : ℂ) := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ p : P,
      (∑ b : Bool,
        (1 / (W p : ℂ)) *
          (if b then (1 : ℂ) else -1) *
          (Complex.I * (c : ℂ) *
            (cot ((if b then α p else -α p) / 2) : ℂ) / (W p : ℂ)) *
        (W p : ℂ))
      = 2 * Complex.I * (c : ℂ) * ((cot (α p / 2) : ℂ) / (W p : ℂ)) := by
    intro p
    have hWp : (W p : ℂ) ≠ 0 := by simpa using hW p
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, if_true, if_false]
    rw [show -α p / 2 = -(α p / 2) by ring, cot_neg]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun p _ => hinner p)]
  rw [← Finset.mul_sum]

theorem lemma_4_2_rotation (P : Type*) [Fintype P] (W α : P → ℝ) (a0 : ℝ)
    (hW : ∀ p, W p ≠ 0) :
    (∑ a : P × Bool,
        (1 / (W a.1 : ℂ)) *
          (if a.2 then (1 : ℂ) else -1) *
          (Complex.I * (a0 : ℂ) *
            (cot ((if a.2 then α a.1 else -α a.1) / 2) : ℂ) / (W a.1 : ℂ)) *
        (W a.1 : ℂ))
      = 2 * Complex.I * (a0 : ℂ) * ∑ p, (cot (α p / 2) : ℂ) / (W p : ℂ) :=
  rotation_overlap_paired P W α a0 hW

theorem corollary_4_6_rotation (P : Type*) [Fintype P] (W α : P → ℝ) (a0 θ : ℝ)
    (hW : ∀ p, W p ≠ 0) :
    (∑ a : P × Bool,
        (1 / (W a.1 : ℂ)) *
          (if a.2 then (1 : ℂ) else -1) *
          (Complex.I * ((a0 * Real.cos θ) : ℂ) *
            (cot ((if a.2 then α a.1 else -α a.1) / 2) : ℂ) / (W a.1 : ℂ)) *
        (W a.1 : ℂ))
      = 2 * Complex.I * ((a0 * Real.cos θ) : ℂ) *
          ∑ p, (cot (α p / 2) : ℂ) / (W p : ℂ) := by
  simpa only [Complex.ofReal_mul] using rotation_overlap_paired P W α (a0 * Real.cos θ) hW

end Qatlib.Papers.HittingTimes08.MainResults
