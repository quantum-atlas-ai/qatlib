/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace Qatlib.Papers.GaussSumEst02.MainResults.Source

def multChar_mul {K : Type*} [Field K] (χ ψ : MultChar K) : MultChar K where
  toFun x := χ.toFun x * ψ.toFun x
  map_zero' := by simp [χ.map_zero', ψ.map_zero']
  map_one' := by simp [χ.map_one', ψ.map_one']
  map_mul' x y := by
    rw [χ.map_mul', ψ.map_mul']
    ring
  norm_eq_one x hx := by
    rw [norm_mul, χ.norm_eq_one x hx, ψ.norm_eq_one x hx, one_mul]

theorem multChar_mul_sum_eq_zero {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (h : (multChar_mul χ ψ).IsNontrivial) :
    (∑ x : K, χ.toFun x * ψ.toFun x) = 0 := by
  obtain ⟨a, ha0, ha⟩ := h
  have hmul : (χ.toFun a * ψ.toFun a) * (∑ x : K, χ.toFun x * ψ.toFun x)
      = ∑ x : K, χ.toFun x * ψ.toFun x := by
    rw [Finset.mul_sum]
    calc ∑ x : K, (χ.toFun a * ψ.toFun a) * (χ.toFun x * ψ.toFun x)
        = ∑ x : K, χ.toFun (a * x) * ψ.toFun (a * x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [χ.map_mul', ψ.map_mul']
          ring
      _ = ∑ x : K, χ.toFun x * ψ.toFun x := by
          simpa using Equiv.sum_comp (Equiv.mulLeft₀ a ha0)
            (fun x : K => χ.toFun x * ψ.toFun x)
  have h2 : (χ.toFun a * ψ.toFun a - 1) * (∑ x : K, χ.toFun x * ψ.toFun x) = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

def jacobiSum {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K) : ℂ :=
  ∑ t : K, χ.toFun t * ψ.toFun (1 - t)

theorem jacobiSum_mul_gaussSum {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (e : AddChar K) (hχ : χ.IsNontrivial) (hψ : ψ.IsNontrivial)
    (hχψ : (multChar_mul χ ψ).IsNontrivial) :
    jacobiSum χ ψ * gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1
      = gaussSum χ.toFun e 1 * gaussSum ψ.toFun e 1 := by
  have hinner : ∀ c : K,
      (∑ a : K, χ.toFun a * ψ.toFun (c - a))
        = (χ.toFun c * ψ.toFun c) * jacobiSum χ ψ := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have hzero : (∑ a : K, χ.toFun a * ψ.toFun (0 - a)) = 0 := by
        calc ∑ a : K, χ.toFun a * ψ.toFun (0 - a)
            = ∑ a : K, χ.toFun a * ψ.toFun (-a) := by simp
          _ = ψ.toFun (-1) * ∑ a : K, χ.toFun a * ψ.toFun a := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [show (-a : K) = (-1) * a by ring, ψ.map_mul']
              ring
          _ = 0 := by rw [multChar_mul_sum_eq_zero χ ψ hχψ, mul_zero]
      rw [hzero]
      simp [χ.map_zero']
    · have hterm : ∀ t : K, χ.toFun (c * t) * ψ.toFun (c - c * t)
          = (χ.toFun c * ψ.toFun c) * (χ.toFun t * ψ.toFun (1 - t)) := by
        intro t
        rw [show c - c * t = c * (1 - t) by ring, ψ.map_mul', χ.map_mul']
        ring
      have hre : (∑ a : K, χ.toFun a * ψ.toFun (c - a))
          = ∑ t : K, (χ.toFun c * ψ.toFun c) * (χ.toFun t * ψ.toFun (1 - t)) := by
        rw [← Equiv.sum_comp (Equiv.mulLeft₀ c hc)
          (fun a => χ.toFun a * ψ.toFun (c - a))]
        exact Finset.sum_congr rfl fun t _ => hterm t
      rw [hre]
      simp only [jacobiSum]
      rw [← Finset.mul_sum]
  have hR : gaussSum χ.toFun e 1 * gaussSum ψ.toFun e 1
      = ∑ c : K, e.toFun c * ((χ.toFun c * ψ.toFun c) * jacobiSum χ ψ) := by
    rw [gaussSum, gaussSum, Fintype.sum_mul_sum]
    simp only [one_mul]
    calc ∑ a : K, ∑ b : K, χ.toFun a * e.toFun a * (ψ.toFun b * e.toFun b)
        = ∑ a : K, ∑ c : K, χ.toFun a * ψ.toFun (c - a) * e.toFun c := by
          refine Finset.sum_congr rfl fun a _ => ?_
          calc ∑ b : K, χ.toFun a * e.toFun a * (ψ.toFun b * e.toFun b)
              = ∑ b : K, χ.toFun a * ψ.toFun (b + a - a) * e.toFun (b + a) := by
                refine Finset.sum_congr rfl fun b _ => ?_
                rw [show b + a - a = b from by ring, e.map_add']
                ring
            _ = ∑ c : K, χ.toFun a * ψ.toFun (c - a) * e.toFun c := by
                simpa using Equiv.sum_comp (Equiv.addRight a)
                  (fun c : K => χ.toFun a * ψ.toFun (c - a) * e.toFun c)
      _ = ∑ c : K, ∑ a : K, χ.toFun a * ψ.toFun (c - a) * e.toFun c :=
          Finset.sum_comm
      _ = ∑ c : K, e.toFun c * ((χ.toFun c * ψ.toFun c) * jacobiSum χ ψ) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [← Finset.sum_mul, hinner c]
          ring
  have hmid : (∑ c : K, e.toFun c * ((χ.toFun c * ψ.toFun c) * jacobiSum χ ψ))
      = jacobiSum χ ψ * gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1 := by
    rw [gaussSum, Finset.mul_sum]
    simp only [one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [← hmid, ← hR]

theorem jacobiSum_eq_div {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (e : AddChar K) (hχ : χ.IsNontrivial) (hψ : ψ.IsNontrivial)
    (hχψ : (multChar_mul χ ψ).IsNontrivial) :
    jacobiSum χ ψ
      = gaussSum χ.toFun e 1 * gaussSum ψ.toFun e 1
        / gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1 := by
  have hne : gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1 ≠ 0 := by
    have hnorm : ‖gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1‖
        = Real.sqrt (Fintype.card K) := by
      simpa [multChar_mul] using
        gaussSum_norm (multChar_mul χ ψ) e hχψ (β := (1 : K)) one_ne_zero
    have hpos : (0 : ℝ) < Real.sqrt (Fintype.card K) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith
  rw [eq_div_iff hne]
  exact jacobiSum_mul_gaussSum χ ψ e hχ hψ hχψ

theorem jacobiSum_norm {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (e : AddChar K) (hχ : χ.IsNontrivial) (hψ : ψ.IsNontrivial)
    (hχψ : (multChar_mul χ ψ).IsNontrivial) :
    ‖jacobiSum χ ψ‖ = Real.sqrt (Fintype.card K) := by
  rw [jacobiSum_eq_div χ ψ e hχ hψ hχψ]
  rw [norm_div, norm_mul,
    gaussSum_norm χ e hχ (β := (1 : K)) one_ne_zero,
    gaussSum_norm ψ e hψ (β := (1 : K)) one_ne_zero]
  have hden : ‖gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1‖
      = Real.sqrt (Fintype.card K) := by
    simpa [multChar_mul] using
      gaussSum_norm (multChar_mul χ ψ) e hχψ (β := (1 : K)) one_ne_zero
  rw [hden]
  have hpos : (0 : ℝ) < Real.sqrt (Fintype.card K) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  field_simp

theorem jacobiSum_polar {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (e : AddChar K) (hχ : χ.IsNontrivial) (hψ : ψ.IsNontrivial)
    (hχψ : (multChar_mul χ ψ).IsNontrivial) :
    ∃ lam : ℝ, jacobiSum χ ψ
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (lam * Complex.I) := by
  have hNpos : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.mpr hNpos
  have hc_ne : ((Real.sqrt (Fintype.card K) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact hsqrt_pos.ne'
  have hunit : ‖jacobiSum χ ψ / ((Real.sqrt (Fintype.card K) : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, jacobiSum_norm χ ψ e hχ hψ hχψ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt_pos, div_self hsqrt_pos.ne']
  obtain ⟨lam, _, hlam⟩ := Complex.norm_eq_one_iff'.mp hunit
  refine ⟨lam, ?_⟩
  rw [hlam]
  field_simp

theorem div_polar_mul {r : ℝ} (hr : ((r : ℝ) : ℂ) ≠ 0) (a b c : ℝ) :
    (((r : ℂ) * Complex.exp (a * Complex.I)) * ((r : ℂ) * Complex.exp (b * Complex.I)))
        / ((r : ℂ) * Complex.exp (c * Complex.I))
      = (r : ℂ) * Complex.exp ((a + b - c) * Complex.I) := by
  have hea : Complex.exp (a * Complex.I) * Complex.exp (b * Complex.I)
      = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hec : Complex.exp ((a + b - c) * Complex.I) * Complex.exp (c * Complex.I)
      = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [div_eq_iff (mul_ne_zero hr (Complex.exp_ne_zero _))]
  have hL : (r : ℂ) * Complex.exp (a * Complex.I)
        * ((r : ℂ) * Complex.exp (b * Complex.I))
      = ((r : ℂ) * r) * Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
    rw [show (r : ℂ) * Complex.exp (a * Complex.I)
          * ((r : ℂ) * Complex.exp (b * Complex.I))
        = ((r : ℂ) * r) * (Complex.exp (a * Complex.I) * Complex.exp (b * Complex.I))
        by ring, hea]
  have hR : (r : ℂ) * Complex.exp ((a + b - c) * Complex.I)
        * ((r : ℂ) * Complex.exp (c * Complex.I))
      = ((r : ℂ) * r) * Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
    rw [show (r : ℂ) * Complex.exp ((a + b - c) * Complex.I)
          * ((r : ℂ) * Complex.exp (c * Complex.I))
        = ((r : ℂ) * r) * (Complex.exp ((a + b - c) * Complex.I)
            * Complex.exp (c * Complex.I)) by ring, hec]
  rw [hL, hR]

theorem exp_angle_prod (a b c : ℝ) :
    Complex.exp (a * Complex.I) * Complex.exp (b * Complex.I)
        * (Complex.exp (c * Complex.I))⁻¹
      = Complex.exp ((a + b - c) * Complex.I) := by
  rw [← Complex.exp_neg]
  rw [← Complex.exp_add (x := (a : ℂ) * Complex.I) (y := (b : ℂ) * Complex.I)]
  rw [show (a : ℂ) * Complex.I + (b : ℂ) * Complex.I = ((a + b : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_inv_sub_inv {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x⁻¹ - y⁻¹‖ = ‖x - y‖ := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    norm_num at hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy
    norm_num at hy
  have h : x⁻¹ - y⁻¹ = (y - x) * (x * y)⁻¹ := by
    field_simp
  rw [h, norm_mul, norm_inv, norm_mul, hx, hy, norm_sub_rev]
  norm_num

theorem norm_mul3_sub_mul3_le {a b c A B C : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) :
    ‖a * b * c - A * B * C‖ ≤ ‖a - A‖ + ‖b - B‖ + ‖c - C‖ := by
  have h : a * b * c - A * B * C
      = (a - A) * (b * c) + A * ((b - B) * c) + A * B * (c - C) := by ring
  rw [h]
  have h1 := norm_add_le ((a - A) * (b * c) + A * ((b - B) * c))
    (A * B * (c - C))
  have h2 := norm_add_le ((a - A) * (b * c)) (A * ((b - B) * c))
  simp only [norm_mul, hb, hc, hA, hB, mul_one, one_mul] at h1 h2 ⊢
  linarith

theorem jacobiSum_phase_exp {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K)
    (e : AddChar K) (hχ : χ.IsNontrivial) (hψ : ψ.IsNontrivial)
    (hχψ : (multChar_mul χ ψ).IsNontrivial)
    {lam γχ γψ γχψ : ℝ}
    (hJ : jacobiSum χ ψ
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (lam * Complex.I))
    (hχg : gaussSum χ.toFun e 1
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γχ * Complex.I))
    (hψg : gaussSum ψ.toFun e 1
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γψ * Complex.I))
    (hχψg : gaussSum (fun x => χ.toFun x * ψ.toFun x) e 1
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γχψ * Complex.I)) :
    Complex.exp (lam * Complex.I)
      = Complex.exp ((γχ + γψ - γχψ) * Complex.I) := by
  have hNpos : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card K) := Real.sqrt_pos.mpr hNpos
  have hc_ne : ((Real.sqrt (Fintype.card K) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact hsqrt_pos.ne'
  apply mul_left_cancel₀ hc_ne
  rw [← hJ, jacobiSum_eq_div χ ψ e hχ hψ hχψ, hχg, hψg, hχψg]
  exact div_polar_mul hc_ne γχ γψ γχψ

end Qatlib.Papers.GaussSumEst02.MainResults.Source
