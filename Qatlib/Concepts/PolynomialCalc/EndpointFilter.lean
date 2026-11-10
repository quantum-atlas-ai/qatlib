/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.ChebyshevScale
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.PolynomialCalc.EndpointFilter
open Qatlib.Concepts.PolynomialCalc.ChebyshevScale

theorem sinh_le_self_mul_cosh {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t * Real.cosh t := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · simp
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u => u * Real.cosh u - Real.sinh u)
      (u * Real.sinh u) u := by
    intro u
    have h1 := (hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)
    simpa using! h1.sub (Real.hasDerivAt_sinh u)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
    (fun u => u * Real.cosh u - Real.sinh u) (fun u => u * Real.sinh u) ht0
    ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    (fun u _ => hderiv u)
  have hceq2 : c * Real.sinh c
      = (t * Real.cosh t - Real.sinh t - (0 * Real.cosh 0 - Real.sinh 0)) / (t - 0) := hceq
  have hpos : 0 ≤ c * Real.sinh c :=
    mul_nonneg hc.1.le (Real.sinh_nonneg_iff.2 hc.1.le)
  have h1 : t * Real.cosh t - Real.sinh t - (0 * Real.cosh 0 - Real.sinh 0)
      = t * (c * Real.sinh c) := by
    have h := (div_eq_iff (sub_ne_zero.2 (ne_of_gt ht0))).1 hceq2.symm
    linarith
  have h0 : (0:ℝ) * Real.cosh 0 - Real.sinh 0 = 0 := by simp
  rw [h0, sub_zero] at h1
  exact le_of_sub_nonneg (by linarith [mul_nonneg ht0.le hpos])

theorem cosh_le_inv_one_sub_half_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.cosh t ≤ 1 / (1 - t ^ 2 / 2) := by
  have hu0 : 0 ≤ t / 2 := by positivity
  set u : ℝ := t / 2 with hu
  have hB0 : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.2 hu0
  have hAB : Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u = 1 := by
    have hh := Real.cosh_sq_sub_sinh_sq u
    ring_nf at hh ⊢
    exact hh
  have hid : Real.cosh t = Real.cosh u * Real.cosh u + Real.sinh u * Real.sinh u := by
    have h1 := Real.cosh_two_mul u
    have h2 : (2:ℝ) * u = t := by rw [hu]; ring
    rw [h2] at h1
    linarith
  have hB2 : Real.sinh u * Real.sinh u ≤ (u * Real.cosh u) * (u * Real.cosh u) :=
    mul_self_le_mul_self hB0 (sinh_le_self_mul_cosh hu0)
  have hu2 : (u * Real.cosh u) * (u * Real.cosh u)
      = (u * u) * (Real.cosh u * Real.cosh u) := by ring
  rw [hu2] at hB2
  have hden : 0 < 1 - t ^ 2 / 2 := by
    have h1 : t * t ≤ 1 := by nlinarith [ht0, ht1]
    linarith
  rw [le_div_iff₀ hden]
  have hX1 : 1 ≤ Real.cosh t := Real.one_le_cosh _
  have hA2 : 2 * (Real.cosh u * Real.cosh u) = Real.cosh t + 1 := by linarith
  have husq : u * u = t ^ 2 / 4 := by rw [hu]; ring
  have hX : Real.cosh t
      ≤ (Real.cosh u * Real.cosh u) * (1 + u * u) := by
    have hA2' : 2 * (Real.cosh u * Real.cosh u) = Real.cosh t + 1 := by linarith
    linarith
  have h1 : Real.cosh t * (1 - u * u) ≤ 1 + u * u := by
    nlinarith [hX, hA2]
  have hfin : Real.cosh t * (1 - t ^ 2 / 2)
      = Real.cosh t * (1 - u * u) - Real.cosh t * (u * u) := by
    rw [husq]; ring
  have huX : u * u ≤ Real.cosh t * (u * u) := by nlinarith [hX1]
  rw [hfin]
  linarith

theorem cosh_le_two_of_le_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.cosh z ≤ 2 := by
  have h1 : z * z ≤ 1 := by nlinarith [hz1, mul_nonneg hz0 (sub_nonneg.2 hz1)]
  have h2 : 0 < 1 - z ^ 2 / 2 := by
    rw [pow_two]
    linarith
  have h := cosh_le_inv_one_sub_half_sq hz0 hz1
  refine le_trans h ?_
  rw [div_le_iff₀ h2, pow_two]
  linarith

theorem cosh_sub_cosh_ge {t z : ℝ} (ht0 : 0 ≤ t) (htz : t ≤ z) :
    t * Real.sinh (z - t) ≤ Real.cosh z - Real.cosh (z - t) := by
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simp
  have hlt : z - t < z := by linarith
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
    (fun u => Real.cosh u) (fun u => Real.sinh u) hlt
    Real.continuous_cosh.continuousOn (fun u _ => Real.hasDerivAt_cosh u)
  have hmul : Real.sinh c * (z - (z - t)) = Real.cosh z - Real.cosh (z - t) :=
    (eq_div_iff (sub_ne_zero.2 (ne_of_gt hlt))).mp hceq
  rw [show z - (z - t) = t from by ring] at hmul
  have hmono : Real.sinh (z - t) ≤ Real.sinh c :=
    Real.sinh_le_sinh.2 hc.1.le
  rw [← hmul, mul_comm (Real.sinh c) t]
  exact mul_le_mul_of_nonneg_left hmono ht0

theorem cosh_ge_one_add_half_sq {t : ℝ} (ht : 0 ≤ t) :
    1 + t * t / 2 ≤ Real.cosh t := by
  have hhalf : Real.cosh t
      = 1 + 2 * (Real.sinh (t / 2) * Real.sinh (t / 2)) := by
    have h1 := Real.cosh_two_mul (t / 2)
    have h2 : (2:ℝ) * (t / 2) = t := by ring
    rw [h2] at h1
    have h3 : Real.cosh (t / 2) * Real.cosh (t / 2)
        - Real.sinh (t / 2) * Real.sinh (t / 2) = 1 := by
      have hh := Real.cosh_sq_sub_sinh_sq (t / 2)
      ring_nf at hh ⊢
      exact hh
    linarith
  have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.2 (by positivity)
  have hL2 : t / 2 * (t / 2) ≤ Real.sinh (t / 2) * Real.sinh (t / 2) :=
    mul_self_le_mul_self (by positivity) hs
  rw [hhalf]
  linarith

theorem half_le_arcosh_sqrt_two : 1 / 2 ≤ Real.arcosh (√2) := by
  have hcosh : Real.cosh (1 / 2) ≤ 8 / 7 := by
    have h := cosh_le_inv_one_sub_half_sq (t := 1 / 2) (by norm_num) (by norm_num)
    have h87 : 1 / (1 - (1 / 2 : ℝ) ^ 2 / 2) = 8 / 7 := by norm_num
    rw [h87] at h
    exact h
  have h87 : 8 / 7 ≤ √2 := by
    have h2 : (√2) * (√2) = 2 := Real.mul_self_sqrt (by norm_num)
    have h0 : (0:ℝ) ≤ 8 / 7 := by norm_num
    have h3 : (0:ℝ) ≤ √2 := by positivity
    have h : 8 / 7 * (8 / 7) ≤ 2 := by norm_num
    nlinarith [h2, h0, h3, h]
  have h12 : Real.arcosh (Real.cosh (1 / 2)) ≤ Real.arcosh (√2) :=
    (Real.arcosh_le_arcosh (Real.cosh_pos _) (by positivity)).2 (le_trans hcosh h87)
  rwa [Real.arcosh_cosh (by norm_num)] at h12

theorem sinh_le_two_mul_of_le_half {rho : ℝ} (hrho0 : 0 ≤ rho)
    (hrholt : rho < 1 / 2) : Real.sinh rho ≤ 2 * rho := by
  have h1 : Real.sinh rho ≤ rho * Real.cosh rho := sinh_le_self_mul_cosh hrho0
  have h2 : Real.cosh rho ≤ 2 := by
    have h := cosh_le_inv_one_sub_half_sq hrho0 (by linarith)
    have hden : 0 < 1 - rho ^ 2 / 2 := by nlinarith [hrholt, hrho0]
    refine le_trans h ?_
    rw [div_le_iff₀ hden]
    nlinarith [hrholt]
  refine le_trans h1 ?_
  rw [mul_comm 2 rho]
  exact mul_le_mul_of_nonneg_left h2 hrho0

theorem ramp_slack {w rho q : ℝ} (hrho0 : 0 ≤ rho)
    (hsinhw : Real.sinh w ≤ Real.cosh w) (hsrhos : Real.sinh rho ≤ 1 - q) :
    q * Real.cosh w ≤ Real.cosh (w - rho) := by
  have h1 : Real.sinh w * Real.sinh rho ≤ Real.cosh w * Real.sinh rho :=
    mul_le_mul_of_nonneg_right hsinhw (Real.sinh_nonneg_iff.2 hrho0)
  have h4 : 1 ≤ Real.cosh rho := Real.one_le_cosh _
  rw [Real.cosh_sub w rho]
  have t2 : Real.cosh w * (Real.cosh rho - Real.sinh rho)
      ≤ Real.cosh w * Real.cosh rho - Real.sinh w * Real.sinh rho := by
    have hz : 0 ≤ Real.sinh rho * (Real.cosh w - Real.sinh w) := by
      nlinarith [h1]
    nlinarith [hz]
  have t3 : q ≤ Real.cosh rho - Real.sinh rho := by nlinarith [h4, hsrhos]
  calc q * Real.cosh w = Real.cosh w * q := mul_comm _ _
    _ ≤ Real.cosh w * (Real.cosh rho - Real.sinh rho) :=
        mul_le_mul_of_nonneg_left t3 (Real.cosh_pos _).le
    _ ≤ Real.cosh w * Real.cosh rho - Real.sinh w * Real.sinh rho := t2

set_option maxHeartbeats 800000 in

theorem per_instance_filter
    (δ ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ p : Polynomial ℝ,
      (p.natDegree : ℝ) ≤ C * Real.rpow δ (-(1 / 2 : ℝ)) * Real.log (1 / ε) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ 1) ∧
      (∀ x : ℝ, -1 ≤ x → x ≤ 1 - δ → |p.eval x| ≤ ε) ∧
      (∀ x : ℝ, 1 - c * δ ≤ x → x ≤ 1 → 1 - ε ≤ p.eval x) := by
  have hsqδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hrw : Real.rpow δ (-(1 / 2 : ℝ)) = 1 / Real.sqrt δ := by
    show (δ ^ (-(1 / 2 : ℝ)) : ℝ) = 1 / Real.sqrt δ
    rw [Real.rpow_neg hδ0.le, ← Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [hrw]
  have hlogpos : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div hε0).2 hε1)
  rcases le_or_gt (1 / 2) ε with hε2 | hε2
  · refine ⟨1 / 2, by norm_num, by norm_num, 1, by norm_num,
      Polynomial.C (min ε 1), ?_, ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_C, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg zero_le_one (le_of_lt (one_div_pos.2 hsqδ))) hlogpos.le
    · intro x _ _
      rw [Polynomial.eval_C, abs_of_nonneg (le_min hε0.le zero_le_one)]
      exact min_le_right _ _
    · intro x _ _
      rw [Polynomial.eval_C, abs_of_nonneg (le_min hε0.le zero_le_one)]
      exact min_le_left _ _
    · intro x _ _
      rw [min_eq_left hε1.le, Polynomial.eval_C]
      linarith
  · set e2 := Real.sqrt ε with he2def
    have he20 : 0 < e2 := Real.sqrt_pos.2 hε0
    have he21 : e2 < 1 := by
      have h := Real.sqrt_lt_sqrt hε0.le hε1
      rwa [Real.sqrt_one] at h
    have he2sq : e2 * e2 = ε := by
      have hh := Real.sq_sqrt hε0.le
      ring_nf at hh ⊢
      exact hh
    have hone : 1 ≤ 1 / e2 := by
      rw [le_div_iff₀ he20]
      linarith

    set w := Real.arcosh (1 / e2) with hwdef
    have hwcos : Real.cosh w = 1 / e2 := Real.cosh_arcosh hone
    have he2s : e2 * √2 ≤ 1 := by
      have h1 : e2 * e2 ≤ 1 / 2 := by rw [he2sq]; linarith
      have hsq2 : (√2) * (√2) = 2 := Real.mul_self_sqrt (by norm_num)
      have hsq : (e2 * √2) ^ 2 ≤ (1:ℝ) ^ 2 := by
        have heq : (e2 * √2) ^ 2 = (e2 * e2) * ((√2) * (√2)) := by ring
        rw [heq, hsq2]
        nlinarith [h1]
      have habs : |e2 * √2| ≤ |(1:ℝ)| := (sq_le_sq).1 hsq
      rwa [abs_of_nonneg (mul_nonneg he20.le (by positivity)), abs_one] at habs
    have hwhalf : 1 / 2 ≤ w := by
      have h2 : √2 ≤ 1 / e2 := by
        rw [le_div_iff₀ he20, mul_comm]
        exact he2s
      have h3 : Real.arcosh (√2) ≤ w :=
        (Real.arcosh_le_arcosh (by positivity) (div_pos (by positivity) he20)).2 h2
      exact le_trans (half_le_arcosh_sqrt_two) h3
    have hw0 : 0 < w := by linarith

    set q := Real.sqrt (1 - ε) with hqdef
    have hq0 : 0 < q := Real.sqrt_pos.2 (by linarith)
    have hqhalf : 1 / 2 ≤ q := by
      have hq2 : q * q = 1 - ε := by
        have hh := Real.sq_sqrt (show (0:ℝ) ≤ 1 - ε by linarith)
        ring_nf at hh ⊢
        exact hh
      nlinarith
    have hq1 : q ≤ 1 := by
      have hh := Real.sqrt_le_sqrt (show (1:ℝ) - ε ≤ 1 by linarith)
      rwa [Real.sqrt_one] at hh
    set rho := (1 - q) / (4 * q) with hrhodef
    have hrho0 : 0 ≤ rho := by
      rw [hrhodef]
      exact div_nonneg (by linarith) (by nlinarith [hqhalf])
    have hrhopos : 0 < rho := by
      have hqq : q * q = 1 - ε := by
        have hh := Real.sq_sqrt (show (0:ℝ) ≤ 1 - ε by linarith)
        ring_nf at hh ⊢
        exact hh
      have hqlt1 : q < 1 := by
        rcases lt_or_ge q 1 with hq | hq
        · exact hq
        · nlinarith [hqq, hq, hqhalf]
      rw [hrhodef]
      exact div_pos (by linarith) (by linarith)
    have hqpos4 : (0:ℝ) < 4 * q := by nlinarith [hqhalf]
    have h2rho : 2 * rho ≤ 1 - q := by
      rw [hrhodef, ← mul_div_assoc, div_le_iff₀ hqpos4]
      nlinarith [hqhalf, hq1]
    have hrholt : rho < 1 / 2 := by
      rw [hrhodef, div_lt_iff₀ hqpos4]
      nlinarith [hqhalf]
    have hrhoW : rho < w := by linarith

    have hsinhw : Real.sinh w ≤ Real.cosh w := by
      have hs1 : Real.sinh w = Real.sqrt ((1 / e2) ^ 2 - 1) := by
        have hh := Real.sinh_arcosh hone
        rwa [← hwdef] at hh
      have hx : (1 / e2) ^ 2 - 1 ≤ (1 / e2) ^ 2 := by linarith
      calc Real.sinh w = Real.sqrt ((1 / e2) ^ 2 - 1) := hs1
        _ ≤ Real.sqrt ((1 / e2) ^ 2) := Real.sqrt_le_sqrt hx
        _ = 1 / e2 := by
            rw [sq]
            exact Real.sqrt_mul_self (by positivity)
        _ = Real.cosh w := hwcos.symm
    have hsinhrho : Real.sinh rho ≤ 2 * rho :=
      sinh_le_two_mul_of_le_half hrho0 hrholt

    have hramp : q * Real.cosh w ≤ Real.cosh (w - rho) :=
      ramp_slack hrho0 hsinhw (le_trans hsinhrho h2rho)

    set k := Nat.ceil (w / Real.sqrt δ) with hkdef
    have hk1 : 1 ≤ k := Nat.ceil_pos.2 (by positivity)
    have hkR : (k : ℝ) ≤ w / Real.sqrt δ + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hw0.le hsqδ.le)).le
    have hkL : w / Real.sqrt δ ≤ (k : ℝ) := by exact_mod_cast Nat.le_ceil _
    set z := (k : ℝ)⁻¹ * w with hzdef
    have hkRne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hk1
    have hz0 : 0 < z := by rw [hzdef]; exact mul_pos (inv_pos.2 hkRpos) hw0
    have hkw : (k : ℝ) * z = w := by
      rw [hzdef, ← mul_assoc, mul_inv_cancel₀ hkRne, one_mul]
    have hzle : z ≤ Real.sqrt δ := by
      have hk : w ≤ (k : ℝ) * Real.sqrt δ := (div_le_iff₀ hsqδ).1 hkL
      rw [hzdef, inv_mul_eq_div, div_le_iff₀ hkRpos]
      linarith
    have hzsqδ : z * z ≤ δ := by
      have h1 : z * z ≤ Real.sqrt δ * Real.sqrt δ :=
        mul_self_le_mul_self hz0.le hzle
      rwa [Real.mul_self_sqrt hδ0.le] at h1
    have hz1 : z < 1 := by
      have h1 : Real.sqrt δ < 1 := by
        have h := Real.sqrt_lt_sqrt hδ0.le hδ1
        rwa [Real.sqrt_one] at h
      linarith

    have hkR1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hzsq4 : δ / 4 ≤ z * z := by
      rcases le_or_gt (Real.sqrt δ) w with hcase | hcase
      · have hwδ1 : 1 ≤ w / Real.sqrt δ := by
          rw [le_div_iff₀ hsqδ, one_mul]
          exact hcase
        have hk2 : (k : ℝ) ≤ 2 * w / Real.sqrt δ := by
          have hsum : w / Real.sqrt δ + w / Real.sqrt δ = 2 * w / Real.sqrt δ := by ring
          linarith
        have hzge : Real.sqrt δ / 2 ≤ z := by
          rw [hzdef, inv_mul_eq_div, le_div_iff₀ hkRpos]
          have hkδ : Real.sqrt δ * (k : ℝ) ≤ 2 * w := by
            rw [mul_comm]
            exact (le_div_iff₀ hsqδ).1 hk2
          have hsplit : Real.sqrt δ / 2 * (k : ℝ)
              = Real.sqrt δ * (k : ℝ) / 2 := by ring
          rw [hsplit, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
          linarith [hkδ]
        have h1 : Real.sqrt δ / 2 * (Real.sqrt δ / 2) ≤ z * z :=
          mul_self_le_mul_self (by positivity) hzge
        have h2 : Real.sqrt δ / 2 * (Real.sqrt δ / 2) = δ / 4 := by
          have hs : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
          have hstep : Real.sqrt δ / 2 * (Real.sqrt δ / 2)
              = Real.sqrt δ * Real.sqrt δ / 4 := by ring
          rw [hstep, hs]
        rw [h2] at h1
        exact h1
      · have hwδ2 : w / Real.sqrt δ ≤ 1 := by
          rw [div_le_iff₀ hsqδ, one_mul]
          exact hcase.le
        have hkl : k ≤ 1 := by
          rw [hkdef, Nat.ceil_le]
          exact_mod_cast hwδ2
        have hkz : k = 1 := le_antisymm hkl hk1
        have hzw : z = w := by rw [hzdef, hkz]; simp
        have hw2 : 1 / 4 ≤ w * w := by
          have hh : (1:ℝ) / 2 * (1 / 2) = 1 / 4 := by norm_num
          rw [← hh]
          exact mul_self_le_mul_self (by norm_num) hwhalf
        have hδ4 : δ / 4 ≤ 1 / 4 := by linarith
        rw [hzw]
        linarith

    have hzc1 : 1 ≤ Real.cosh z := Real.one_le_cosh _
    have hzc2 : Real.cosh z ≤ 2 := cosh_le_two_of_le_one hz0.le hz1.le
    have hzsqrt : Real.sqrt δ / 2 ≤ z := by
      have hpos : (0:ℝ) ≤ Real.sqrt δ / 2 := by positivity
      have hsq : Real.sqrt δ / 2 * (Real.sqrt δ / 2) = δ / 4 := by
        have hs : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
        have hstep : Real.sqrt δ / 2 * (Real.sqrt δ / 2)
            = Real.sqrt δ * Real.sqrt δ / 4 := by ring
        rw [hstep, hs]
      have h2 : Real.sqrt δ / 2 = Real.sqrt (δ / 4) := by
        rw [← hsq]
        exact (Real.sqrt_mul_self hpos).symm
      rw [h2, ← Real.sqrt_mul_self hz0.le]
      exact Real.sqrt_le_sqrt hzsq4

    set la := (Real.cosh z + 1) / 2 with hladef
    have hla1 : (1:ℝ) ≤ la := by
      rw [hladef]
      linarith
    have hla0 : 0 < la := lt_of_lt_of_le zero_lt_one hla1
    have hla32 : la ≤ 3 / 2 := by
      rw [hladef]
      linarith
    set b := Real.cosh z - la with hbdef
    set gp := Polynomial.C la * (Polynomial.X + Polynomial.C (b / la)) with hgpdef
    have hgpe (x : ℝ) : gp.eval x = Real.cosh z - la * (1 - x) := by
      rw [hgpdef, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C, hbdef]
      field_simp [hla0.ne']; ring
    have hgpdeg : gp.natDegree = 1 := by
      have hXCne : Polynomial.X + Polynomial.C (b / la) ≠ 0 := by
        intro h0
        have h1 : (Polynomial.X + Polynomial.C (b / la)).natDegree = 1 :=
          Polynomial.natDegree_X_add_C (b / la)
        rw [h0, Polynomial.natDegree_zero] at h1
        exact absurd h1 (by norm_num)
      rw [hgpdef, Polynomial.natDegree_mul (Polynomial.C_ne_zero.2 hla0.ne') hXCne,
        Polynomial.natDegree_C, Polynomial.natDegree_X_add_C, zero_add]

    have hczδ : Real.cosh z ≤ 2 / (2 - δ) := by
      have hsq2 : z ^ 2 ≤ δ := by rw [pow_two]; exact hzsqδ
      have h := cosh_le_inv_one_sub_half_sq hz0.le hz1.le
      have hden : (0:ℝ) < 1 - δ / 2 := by linarith
      have hstep1 : 1 / (1 - z ^ 2 / 2) ≤ 1 / (1 - δ / 2) :=
        one_div_le_one_div_of_le hden (by linarith)
      have hstep2 : 1 / (1 - δ / 2) = 2 / (2 - δ) := by
        field_simp
      exact le_trans (le_trans h hstep1) (le_of_eq hstep2)
    have hband1 : Real.cosh z - 1 ≤ la * δ := by
      have hpos2δ : (0:ℝ) < 2 - δ := by linarith
      have hc2 : Real.cosh z * (2 - δ) ≤ 2 := (le_div_iff₀ hpos2δ).1 hczδ
      rw [hladef]
      linarith

    set c := min (1 / 12) (rho / (12 * (w + 1))) with hcdef
    have hc0 : 0 < c := by
      refine lt_min (by norm_num : (0:ℝ) < 1 / 12) ?_
      exact div_pos hrhopos (by positivity)
    have hc1 : c < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)

    have hrho4 : rho ≤ 1 / 4 := by linarith [h2rho, hqhalf]
    set tt := rho / (k : ℝ) with httdef
    have hzkw : (z / 2) * (k : ℝ) = w / 2 := by
      rw [div_mul_eq_mul_div, mul_comm, ← hkw]
    have httz : tt ≤ z / 2 := by
      rw [httdef, div_le_iff₀ hkRpos, hzkw, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith [hrho4]
    have hs0 : 0 ≤ tt := div_nonneg hrho0 hkRpos.le
    have hstz : tt ≤ z := by linarith [httz]
    have hztt : (0:ℝ) ≤ z - tt := by linarith [httz, hz0]
    have hksqδ : (k : ℝ) * Real.sqrt δ ≤ w + 1 := by
      have h2 : (w / Real.sqrt δ + 1) * Real.sqrt δ = w + Real.sqrt δ := by
        field_simp [hsqδ.ne']
      calc (k : ℝ) * Real.sqrt δ ≤ (w / Real.sqrt δ + 1) * Real.sqrt δ :=
            mul_le_mul_of_nonneg_right hkR hsqδ.le
        _ = w + Real.sqrt δ := h2
        _ ≤ w + 1 := by
            have h3 := Real.sqrt_le_sqrt hδ1.le
            rw [Real.sqrt_one] at h3
            linarith
    have hslack : la * c * δ ≤ Real.cosh z - Real.cosh (z - tt) := by
      have hMVT : tt * Real.sinh (z - tt) ≤ Real.cosh z - Real.cosh (z - tt) :=
        cosh_sub_cosh_ge hs0 hstz
      have hs2 : z - tt ≤ Real.sinh (z - tt) := Real.self_le_sinh_iff.2 hztt
      have hs3 : tt * (z - tt) ≤ tt * Real.sinh (z - tt) :=
        mul_le_mul_of_nonneg_left hs2 hs0
      have hzt2 : z / 2 ≤ z - tt := by linarith [httz]
      have hlower : tt * (z / 2) ≤ tt * (z - tt) := mul_le_mul_of_nonneg_left hzt2 hs0
      have hc12r : c ≤ rho / (12 * (w + 1)) := min_le_right _ _
      have hA : la * c * δ ≤ rho * δ / (8 * (w + 1)) := by
        have hstep1 : la * (c * δ) ≤ (3 / 2) * (rho / (12 * (w + 1)) * δ) :=
          calc la * (c * δ) ≤ (3 / 2) * (c * δ) :=
                mul_le_mul_of_nonneg_right hla32 (mul_nonneg hc0.le hδ0.le)
            _ ≤ (3 / 2) * (rho / (12 * (w + 1)) * δ) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc12r hδ0.le)
                  (by positivity)
        rw [show la * c * δ = la * (c * δ) from by ring,
          le_div_iff₀ (by positivity : (0:ℝ) < 8 * (w + 1))]
        have h2 : la * (c * δ) * (8 * (w + 1))
            ≤ (3 / 2) * (rho / (12 * (w + 1)) * δ) * (8 * (w + 1)) :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
        have h3 : (3 / 2 : ℝ) * (rho / (12 * (w + 1)) * δ) * (8 * (w + 1))
            ≤ rho * δ := by
          rw [show (3 / 2 : ℝ) * (rho / (12 * (w + 1)) * δ) * (8 * (w + 1))
              = rho * δ from by
              field_simp [(show (0:ℝ) < 12 * (w + 1) by positivity).ne']
              ring]
        exact le_trans h2 h3
      have hkδ : (2:ℝ) * (k : ℝ) * δ ≤ 8 * (w + 1) * z := by
        have hsd2 : Real.sqrt δ ≤ 2 * z := by linarith [hzsqrt]
        have h1 : (2:ℝ) * (k : ℝ) * Real.sqrt δ ≤ 2 * (w + 1) := by
          have h2 := hksqδ
          linarith [h2]
        have hlhs : ((2:ℝ) * (k : ℝ) * Real.sqrt δ) * Real.sqrt δ
            = (2:ℝ) * (k : ℝ) * δ := by
          simp only [mul_assoc, Real.mul_self_sqrt hδ0.le]
        have hprod : ((2:ℝ) * (k : ℝ) * Real.sqrt δ) * Real.sqrt δ
            ≤ (2 * (w + 1)) * (2 * z) :=
          mul_le_mul h1 hsd2 hsqδ.le (by positivity)
        have hfin : (2 * (w + 1)) * (2 * z) ≤ 8 * (w + 1) * z := by
          have hnn : (0:ℝ) ≤ 4 * ((w + 1) * z) :=
            mul_nonneg (by norm_num) (mul_nonneg (by linarith) hz0.le)
          linarith
        rw [← hlhs]
        exact le_trans hprod hfin
      have hB : rho * δ / (8 * (w + 1)) ≤ rho * z / (2 * (k : ℝ)) := by
        have hkey2 : rho * δ * (2 * (k : ℝ)) ≤ rho * z * (8 * (w + 1)) := by
          calc rho * δ * (2 * (k : ℝ)) = rho * ((2:ℝ) * (k : ℝ) * δ) := by ring
            _ ≤ rho * (8 * (w + 1) * z) := mul_le_mul_of_nonneg_left hkδ hrho0
            _ = rho * z * (8 * (w + 1)) := by ring
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (k : ℝ))]
        rw [show rho * δ / (8 * (w + 1)) * (2 * (k : ℝ))
            = rho * δ * (2 * (k : ℝ)) / (8 * (w + 1)) from by ring,
          div_le_iff₀ (by positivity : (0:ℝ) < 8 * (w + 1))]
        exact hkey2
      have hC : rho * z / (2 * (k : ℝ)) = tt * (z / 2) := by
        rw [httdef]
        ring
      calc la * c * δ ≤ rho * δ / (8 * (w + 1)) := hA
        _ ≤ rho * z / (2 * (k : ℝ)) := hB
        _ = tt * (z / 2) := hC
        _ ≤ tt * (z - tt) := hlower
        _ ≤ tt * Real.sinh (z - tt) := hs3
        _ ≤ Real.cosh z - Real.cosh (z - tt) := hMVT

    have hzcosh : hyperbolicScale ((k : ℝ))⁻¹ (1 / e2) = Real.cosh z := by
      conv_lhs => unfold hyperbolicScale
    have hTc : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (hyperbolicScale ((k : ℝ))⁻¹ (1 / e2))
        = 1 / e2 :=
      eval_T_band_const e2 k
        (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hk1))
        he20 he21.le
    have hTc2 : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cosh z) = 1 / e2 := by
      rw [← hzcosh]
      exact hTc
    refine ⟨c, hc0, hc1, (2 * w + 2) / Real.log (1 / ε),
      div_pos (by linarith) hlogpos,
      (Polynomial.C e2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp gp) ^ 2,
      ?_, ?_, ?_, ?_⟩
    · have hTne : (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp gp ≠ 0 := by
        intro h0
        have h1 : ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp gp).eval 1 = 1 / e2 := by
          rw [Polynomial.eval_comp, hgpe, sub_self, mul_zero, sub_zero, hTc2]
        rw [h0, Polynomial.eval_zero] at h1
        exact absurd h1.symm (one_div_ne_zero he20.ne')
      have hTdeg : ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp gp).natDegree = k := by
        rw [Polynomial.natDegree_comp, Polynomial.Chebyshev.natDegree_T,
          hgpdeg, mul_one]
        omega
      have hdeg : ((Polynomial.C e2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp gp) ^ 2).natDegree
          = k * 2 := by
        rw [Polynomial.natDegree_pow,
          Polynomial.natDegree_mul (Polynomial.C_ne_zero.2 he20.ne') hTne,
          Polynomial.natDegree_C, hTdeg, zero_add]
        omega
      have hR : (2 * w + 2) / Real.log (1 / ε) * (1 / Real.sqrt δ) * Real.log (1 / ε)
          = (2 * w + 2) / Real.sqrt δ := by
        field_simp
      have hsqrt1 : Real.sqrt δ ≤ 1 := by
        have h := Real.sqrt_le_sqrt hδ1.le
        rwa [Real.sqrt_one] at h
      have h11 : 1 ≤ 1 / Real.sqrt δ := by
        rw [le_div_iff₀ hsqδ, one_mul]
        exact hsqrt1
      rw [hdeg, hR, Nat.cast_mul]
      calc (k : ℝ) * 2 ≤ (w / Real.sqrt δ + 1) * 2 :=
            mul_le_mul_of_nonneg_right hkR (by norm_num : (0:ℝ) ≤ 2)
        _ = 2 * w / Real.sqrt δ + 1 * 2 := by ring
        _ ≤ 2 * w / Real.sqrt δ + (1 / Real.sqrt δ) * 2 :=
            add_le_add_right (mul_le_mul_of_nonneg_right h11 (by norm_num : (0:ℝ) ≤ 2))
              (2 * w / Real.sqrt δ)
        _ = (2 * w + 2) / Real.sqrt δ := by
            field_simp
    · intro x hx1 hx2
      have hgx1 : gp.eval x ≤ Real.cosh z := by
        rw [hgpe]
        have h1 : (0:ℝ) ≤ la * (1 - x) := mul_nonneg hla0.le (by linarith)
        linarith
      have hgx2 : (-1:ℝ) ≤ gp.eval x := by
        rw [hgpe]
        have h1 : la * (1 - x) ≤ la * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hla0.le
        have h3 : la * 2 ≤ Real.cosh z + 1 := by
          rw [hladef]
          linarith
        linarith
      have habs : |gp.eval x| ≤ Real.cosh z := by
        refine abs_le.2 ⟨?_, hgx1⟩
        have h1 : (1:ℝ) ≤ Real.cosh z := Real.one_le_cosh _
        linarith
      have hmon : |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|
          ≤ (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cosh z) :=
        abs_T_le_T_of_abs_le (k : ℤ) (by exact_mod_cast Nat.zero_le k) hzc1 habs
      rw [Polynomial.eval_pow, abs_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_comp, abs_mul, abs_of_pos he20]
      have h1 : e2 * |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)| ≤ 1 := by
        refine (mul_le_mul_of_nonneg_left hmon he20.le).trans_eq ?_
        rw [hTc2]
        field_simp
      rw [pow_two]
      have h2 := mul_self_le_mul_self (mul_nonneg he20.le (abs_nonneg _)) h1
      rwa [one_mul] at h2
    · intro x hx1 hx2
      have hgx1 : gp.eval x ≤ 1 := by
        rw [hgpe]
        have hxbound : la * δ ≤ la * (1 - x) :=
          mul_le_mul_of_nonneg_left (by linarith) hla0.le
        linarith
      have hgx2 : (-1:ℝ) ≤ gp.eval x := by
        rw [hgpe]
        have h1 : la * (1 - x) ≤ la * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hla0.le
        have h3 : la * 2 ≤ Real.cosh z + 1 := by
          rw [hladef]
          linarith
        linarith
      have hT : |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)| ≤ 1 :=
        abs_T_le_one_of_abs_le_one (k : ℤ) (gp.eval x) (abs_le.2 ⟨hgx2, hgx1⟩)
      rw [Polynomial.eval_pow, abs_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_comp, abs_mul, abs_of_pos he20]
      have hTabs : (|(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|)
          * (|(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|) ≤ 1 * 1 :=
        mul_self_le_mul_self (abs_nonneg _) hT
      rw [one_mul] at hTabs
      rw [pow_two]
      rw [show (e2 * |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|)
          * (e2 * |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|)
          = (e2 * e2) * (|(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|
            * |(Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)|) from by ring]
      rw [he2sq]
      exact (mul_le_mul_of_nonneg_left hTabs hε0.le).trans_eq (mul_one ε)
    · intro x hx1 hx2
      have hy0ge1 : (1:ℝ) ≤ Real.cosh z - la * (c * δ) := by
        have hc12 : c ≤ 1 / 12 := min_le_left _ _
        have h1 : la * (c * δ) ≤ δ / 8 := by
          have hs1 : la * (c * δ) ≤ (3 / 2) * ((1 / 12) * δ) :=
            calc la * (c * δ) ≤ (3 / 2) * (c * δ) :=
                  mul_le_mul_of_nonneg_right hla32 (mul_nonneg hc0.le hδ0.le)
              _ ≤ (3 / 2) * ((1 / 12) * δ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc12 hδ0.le)
                    (by positivity)
          exact hs1.trans_eq (by ring : (3 / 2 : ℝ) * ((1 / 12) * δ) = δ / 8)
        have h2 : δ / 8 ≤ Real.cosh z - 1 := by
          have h3 : 1 + z * z / 2 ≤ Real.cosh z := cosh_ge_one_add_half_sq hz0.le
          linarith [hzsq4]
        linarith
      have hy1m : Real.cosh z - la * (c * δ) ≤ gp.eval x := by
        rw [hgpe]
        have hle : 1 - x ≤ c * δ := by linarith
        have h1 : la * (1 - x) ≤ la * (c * δ) := mul_le_mul_of_nonneg_left hle hla0.le
        linarith
      have hyx1 : (1:ℝ) ≤ gp.eval x := le_trans hy0ge1 hy1m
      have hyx1pos : (0:ℝ) < gp.eval x := lt_of_lt_of_le zero_lt_one hyx1
      have haxge : Real.cosh (z - tt) ≤ gp.eval x := by linarith [hslack, hy1m]
      have harc : z - tt ≤ Real.arcosh (gp.eval x) := by
        have h1 : Real.arcosh (Real.cosh (z - tt)) ≤ Real.arcosh (gp.eval x) :=
          (Real.arcosh_le_arcosh (Real.cosh_pos _) hyx1pos).2 haxge
        rwa [Real.arcosh_cosh hztt] at h1
      have hTeq : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)
          = Real.cosh (((k : ℤ) : ℝ) * Real.arcosh (gp.eval x)) := by
        have hh := Polynomial.Chebyshev.T_real_cosh (Real.arcosh (gp.eval x)) (k : ℤ)
        rwa [Real.cosh_arcosh hyx1] at hh
      have hkcast : (((k : ℤ) : ℝ)) = ((k : ℝ)) := by exact_mod_cast rfl
      have hklz : ((k : ℤ) : ℝ) * (z - tt) = w - rho := by
        rw [hkcast, httdef]
        field_simp
        linarith [hkw]
      have hTlb : Real.cosh (w - rho)
          ≤ (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x) := by
        have hnn1 : (0:ℝ) ≤ ((k : ℤ) : ℝ) * Real.arcosh (gp.eval x) :=
          mul_nonneg (by positivity) (Real.arcosh_nonneg hyx1)
        have hnn2 : (0:ℝ) ≤ w - rho := by linarith [hrhoW]
        rw [hTeq, Real.cosh_le_cosh, abs_of_nonneg hnn2, abs_of_nonneg hnn1, ← hklz]
        exact mul_le_mul_of_nonneg_left harc (by positivity)
      have h1 : q * (1 / e2) ≤ Real.cosh (w - rho) := by
        have h2 := hramp
        rw [hwcos] at h2
        exact h2
      have hval : q ≤ e2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x) := by
        have hqe : q = e2 * (q * (1 / e2)) := by field_simp
        rw [hqe]
        exact mul_le_mul_of_nonneg_left (le_trans h1 hTlb) he20.le
      rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_comp, pow_two]
      have hqq : q * q = 1 - ε := by
        have hh := Real.sq_sqrt (show (0:ℝ) ≤ 1 - ε by linarith)
        ring_nf at hh ⊢
        exact hh
      calc 1 - ε = q * q := hqq.symm
        _ ≤ (e2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x))
              * (e2 * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (gp.eval x)) :=
              mul_self_le_mul_self hq0.le hval

end Qatlib.Concepts.PolynomialCalc.EndpointFilter
