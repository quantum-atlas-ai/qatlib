/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators

def oddIdx (N : ℕ) : Finset (Idx N) :=
  Finset.univ.filter (fun p => (p : ℕ) % 2 = 1)

noncomputable def sinSum (N : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ p ∈ oddIdx N, (Real.sin (Real.pi * (p : ℝ) / (2 * (N : ℝ))))⁻¹

lemma queryAmp_norm_odd {N : ℕ} (_hN : 0 < N) {p q : Idx N}
    (hpq : ((p : ℕ) + (q : ℕ)) % 2 = 1) :
    ‖queryAmp N p q‖ = (1 / (N : ℝ)) * |Real.sin (momAngle N p q)|⁻¹ := by
  unfold queryAmp
  rw [if_pos hpq]
  simp only [norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

lemma queryAmp_eq_zero {N : ℕ} {p q : Idx N}
    (h : ((p : ℕ) + (q : ℕ)) % 2 ≠ 1) : queryAmp N p q = 0 := by
  unfold queryAmp
  rw [if_neg h]

def reflect (N : ℕ) (q : Idx N) (p : Idx N) : Idx N :=
  ⟨(q.val + 2 * N - p.val) % (2 * N), Nat.mod_lt _ (by have := p.isLt; omega)⟩

lemma reflect_val (N : ℕ) (q p : Idx N) :
    (reflect N q p).val = (q.val + 2 * N - p.val) % (2 * N) := rfl

lemma reflect_involutive (N : ℕ) (q : Idx N) : Function.Involutive (reflect N q) := by
  intro p
  apply Fin.ext
  rw [reflect_val, reflect_val]
  set c := q.val + 2 * N - p.val with hcdef
  set k := c / (2 * N) with hkdef
  have hc : c = c % (2 * N) + k * (2 * N) := by
    rw [hkdef, Nat.mod_add_div']
  have hcp : c + p.val = q.val + 2 * N := by omega
  have hkey : q.val + 2 * N - c % (2 * N) = k * (2 * N) + p.val := by
    omega
  rw [hkey]
  rw [Nat.mul_add_mod' k (2 * N) p.val]
  exact Nat.mod_eq_of_lt p.isLt

def zidx (N : ℕ) (hN : 0 < N) : Idx N := ⟨0, by omega⟩

lemma zidx_val (N : ℕ) (hN : 0 < N) : (zidx N hN).val = 0 := rfl

lemma momAngle_val (N : ℕ) (p q : Idx N) :
    momAngle N p q = Real.pi * ((q.val : ℝ) - (p.val : ℝ)) / (2 * (N : ℝ)) := rfl

lemma reflect_sin_abs (N : ℕ) (hN : 0 < N) (q p : Idx N) :
    |Real.sin (momAngle N p q)| = |Real.sin (momAngle N (reflect N q p) (zidx N hN))| := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  by_cases hle : p.val ≤ q.val
  · have hrv : (reflect N q p).val = q.val - p.val := by
      rw [reflect_val]
      have h : q.val + 2 * N - p.val = 1 * (2 * N) + (q.val - p.val) := by omega
      rw [h, Nat.mul_add_mod' 1 (2 * N) (q.val - p.val)]
      exact Nat.mod_eq_of_lt (by omega)
    have hneg : momAngle N p q = - momAngle N (reflect N q p) (zidx N hN) := by
      rw [momAngle_val, momAngle_val, zidx_val, hrv, Nat.cast_sub hle]
      field_simp
      ring
    rw [hneg, Real.sin_neg, abs_neg]
  · have hlt : q.val < p.val := by omega
    have hle2 : p.val ≤ q.val + 2 * N := by omega
    have hrv : (reflect N q p).val = q.val + 2 * N - p.val := by
      rw [reflect_val, Nat.mod_eq_of_lt]
      omega
    have heq : Real.sin (momAngle N p q) =
        Real.sin (momAngle N (reflect N q p) (zidx N hN)) := by
      have h : momAngle N p q = -(momAngle N (reflect N q p) (zidx N hN)) - Real.pi := by
        rw [momAngle_val, momAngle_val, zidx_val, hrv, Nat.cast_sub hle2]
        push_cast
        field_simp
        ring
      rw [h, show -(momAngle N (reflect N q p) (zidx N hN)) - Real.pi =
            -((momAngle N (reflect N q p) (zidx N hN)) + Real.pi) by ring,
        Real.sin_neg, Real.sin_add_pi, neg_neg]
    rw [heq]

lemma reflect_parity (N : ℕ) (_hN : 0 < N) (q p : Idx N) :
    (reflect N q p).val % 2 = (p.val + q.val) % 2 := by
  rw [reflect_val]
  have hdvd : 2 ∣ 2 * N := ⟨N, by ring⟩
  rw [Nat.mod_mod_of_dvd _ hdvd]
  omega

lemma queryAmp_norm_reflect (N : ℕ) (hN : 0 < N) (q p : Idx N) :
    ‖queryAmp N p q‖ = ‖queryAmp N (reflect N q p) (zidx N hN)‖ := by
  have hp := reflect_parity N hN q p
  by_cases hpq : (p.val + q.val) % 2 = 1
  · have hr : ((reflect N q p).val + (zidx N hN).val) % 2 = 1 := by
      rw [zidx_val, Nat.add_zero]
      rw [hp]; exact hpq
    rw [queryAmp_norm_odd hN hpq, queryAmp_norm_odd hN hr]
    rw [reflect_sin_abs N hN q p]
  · have hr : ((reflect N q p).val + (zidx N hN).val) % 2 ≠ 1 := by
      rw [zidx_val, Nat.add_zero, hp]; exact hpq
    rw [queryAmp_eq_zero hpq, queryAmp_eq_zero hr]

lemma sum_qnorm_shift (N : ℕ) (hN : 0 < N) (q : Idx N) :
    (∑ p : Idx N, ‖queryAmp N p q‖)
      = ∑ p : Idx N, ‖queryAmp N p (zidx N hN)‖ := by
  refine Finset.sum_bij (fun p _ => reflect N q p) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro a _ b _ hab
    have hab' : reflect N q a = reflect N q b := hab
    rw [← reflect_involutive N q a, ← reflect_involutive N q b, hab']
  · intro b _
    exact ⟨reflect N q b, Finset.mem_univ _, reflect_involutive N q b⟩
  · intro p _
    exact queryAmp_norm_reflect N hN q p

lemma sum_qnorm_zero (N : ℕ) (hN : 0 < N) :
    (∑ p : Idx N, ‖queryAmp N p (zidx N hN)‖) = sinSum N := by
  have hterm : ∀ p : Idx N, ‖queryAmp N p (zidx N hN)‖ =
      if p.val % 2 = 1 then
        (1 / (N : ℝ)) * (Real.sin (Real.pi * (p.val : ℝ) / (2 * (N : ℝ))))⁻¹
      else 0 := by
    intro p
    by_cases hp : p.val % 2 = 1
    · rw [if_pos hp]
      have hcond : ((p : ℕ) + (zidx N hN : ℕ)) % 2 = 1 := by
        rw [zidx_val, Nat.add_zero]; exact hp
      rw [queryAmp_norm_odd hN hcond]
      have hp0 : 0 < p.val := Nat.pos_of_ne_zero (by intro h; rw [h] at hp; simp at hp)
      have hpos : 0 < Real.pi * (p.val : ℝ) / (2 * (N : ℝ)) := by
        have : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast hp0
        positivity
      have hlt : Real.pi * (p.val : ℝ) / (2 * (N : ℝ)) < Real.pi := by
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (N:ℝ))]
        have h2 : (p.val:ℝ) < 2 * (N:ℝ) := by exact_mod_cast p.isLt
        nlinarith [Real.pi_pos]
      have habs : |Real.sin (momAngle N p (zidx N hN))| =
          Real.sin (Real.pi * (p.val : ℝ) / (2 * (N : ℝ))) := by
        rw [momAngle_val, zidx_val]
        simp only [Nat.cast_zero]
        have harg : Real.pi * ((0:ℝ) - (p.val:ℝ)) / (2*(N:ℝ)) =
            -(Real.pi*(p.val:ℝ)/(2*(N:ℝ))) := by ring
        rw [harg, Real.sin_neg, abs_neg,
          abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hpos hlt)]
      rw [habs]
    · rw [if_neg hp]
      have hfalse : ((p : ℕ) + (zidx N hN : ℕ)) % 2 ≠ 1 := by
        rw [zidx_val, Nat.add_zero]; exact hp
      rw [queryAmp_eq_zero hfalse]
      simp
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  unfold sinSum oddIdx
  rw [← Finset.sum_filter]
  rw [Finset.mul_sum]

lemma queryAmp_norm_sum (N : ℕ) (hN : 0 < N) (q : Idx N) :
    (∑ p : Idx N, ‖queryAmp N p q‖) = sinSum N := by
  rw [sum_qnorm_shift N hN q, sum_qnorm_zero N hN]

lemma sinSum_nonneg (N : ℕ) (hN : 0 < N) : 0 ≤ sinSum N := by
  unfold sinSum oddIdx
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro p hp
  rw [Finset.mem_filter] at hp
  apply inv_nonneg.mpr
  apply le_of_lt
  apply Real.sin_pos_of_pos_of_lt_pi
  · have hp1 : 0 < p.val := by
      rcases Nat.eq_zero_or_pos p.val with h | h
      · rw [h] at hp; simp at hp
      · exact h
    have : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast hp1
    positivity
  · rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (N:ℝ))]
    have h2 : (p.val:ℝ) < 2 * (N:ℝ) := by exact_mod_cast p.isLt
    nlinarith [Real.pi_pos]

lemma queryStep_l1 (N : ℕ) (hN : 0 < N) (a : Idx N → ℂ) :
    (∑ p : Idx N, ‖queryStep N a p‖) ≤ sinSum N * ∑ q : Idx N, ‖a q‖ := by
  have hstep : ∀ p : Idx N, ‖queryStep N a p‖ ≤ ∑ q : Idx N, ‖queryAmp N p q‖ * ‖a q‖ := by
    intro p
    unfold queryStep
    calc ‖∑ q, queryAmp N p q * a q‖ ≤ ∑ q, ‖queryAmp N p q * a q‖ := norm_sum_le _ _
      _ = ∑ q, ‖queryAmp N p q‖ * ‖a q‖ := by simp only [norm_mul]
  calc ∑ p, ‖queryStep N a p‖ ≤ ∑ p, ∑ q, ‖queryAmp N p q‖ * ‖a q‖ :=
        Finset.sum_le_sum (fun p _ => hstep p)
    _ = ∑ q, ∑ p, ‖queryAmp N p q‖ * ‖a q‖ := Finset.sum_comm
    _ = ∑ q, (∑ p, ‖queryAmp N p q‖) * ‖a q‖ := by
        apply Finset.sum_congr rfl; intro q _; rw [Finset.sum_mul]
    _ = ∑ q, sinSum N * ‖a q‖ := by
        apply Finset.sum_congr rfl; intro q _
        rw [queryAmp_norm_sum N hN q]
    _ = sinSum N * ∑ q, ‖a q‖ := by rw [Finset.mul_sum]

lemma phaseApply_norm {N : ℕ} (α : Idx N → ℝ) (a : Idx N → ℂ) (p : Idx N) :
    ‖phaseApply α a p‖ = ‖a p‖ := by
  unfold phaseApply
  rw [norm_mul]
  have hexp : ‖Complex.exp (Complex.I * ((α p : ℝ) : ℂ))‖ = 1 := by
    rw [show Complex.I * ((α p : ℝ) : ℂ) = ((α p : ℝ) : ℂ) * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, one_mul]

lemma startState_l1 (N : ℕ) (hN : 0 < N) :
    (∑ p : Idx N, ‖startState N p‖) = 1 := by
  have hf : ∀ p : Idx N, ‖startState N p‖ = if p.val = 0 then (1:ℝ) else 0 := by
    intro p
    unfold startState
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun p _ => hf p)]
  rw [Finset.sum_eq_single (zidx N hN)]
  · rw [zidx_val]; simp
  · intro b _ hb
    rw [if_neg]
    intro h; exact hb (Fin.ext (by rw [zidx_val, h]))
  · intro h; exact absurd (Finset.mem_univ _) h

lemma psi_l1 (N : ℕ) (hN : 0 < N) (α : ℕ → Idx N → ℝ) :
    ∀ ℓ : ℕ, (∑ p : Idx N, ‖psi N α ℓ p‖) ≤ (sinSum N) ^ ℓ
  | 0 => by
      rw [show psi N α 0 = startState N from rfl, startState_l1 N hN, pow_zero]
  | ℓ + 1 => by
      have hS : 0 ≤ sinSum N := sinSum_nonneg N hN
      calc ∑ p, ‖psi N α (ℓ+1) p‖
          = ∑ p, ‖queryStep N (psi N α ℓ) p‖ := by
              apply Finset.sum_congr rfl; intro p _
              rw [show psi N α (ℓ+1) = phaseApply (α (ℓ+1)) (queryStep N (psi N α ℓ)) from rfl,
                phaseApply_norm]
        _ ≤ sinSum N * ∑ q, ‖psi N α ℓ q‖ := queryStep_l1 N hN _
        _ ≤ sinSum N * (sinSum N) ^ ℓ :=
              mul_le_mul_of_nonneg_left (psi_l1 N hN α ℓ) hS
        _ = (sinSum N) ^ (ℓ + 1) := by rw [pow_succ]; ring

lemma targetAmp_norm (N parity : ℕ) (_hN : 0 < N) (p : Idx N) :
    ‖targetAmp N parity p‖ = if p.val % 2 = parity then ((Real.sqrt (N:ℝ))⁻¹) else 0 := by
  unfold targetAmp
  split_ifs <;> simp [Real.sqrt_nonneg]

lemma successAmplitude_bound (N k : ℕ) (hN : 0 < N) (α : ℕ → Idx N → ℝ) :
    ‖successAmplitude N k α‖ ≤ ((Real.sqrt (N:ℝ))⁻¹) * (sinSum N) ^ k := by
  unfold successAmplitude
  calc ‖∑ p, star (targetAmp N (k % 2) p) * psi N α k p‖
      ≤ ∑ p, ‖star (targetAmp N (k % 2) p) * psi N α k p‖ := norm_sum_le _ _
    _ = ∑ p, ‖targetAmp N (k % 2) p‖ * ‖psi N α k p‖ := by simp only [norm_mul, norm_star]
    _ ≤ ∑ p, ((Real.sqrt (N:ℝ))⁻¹) * ‖psi N α k p‖ := by
        apply Finset.sum_le_sum; intro p _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [targetAmp_norm N (k % 2) hN p]
        split_ifs
        · exact le_rfl
        · exact le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
    _ = ((Real.sqrt (N:ℝ))⁻¹) * ∑ p, ‖psi N α k p‖ := by rw [Finset.mul_sum]
    _ ≤ ((Real.sqrt (N:ℝ))⁻¹) * (sinSum N) ^ k := by
        apply mul_le_mul_of_nonneg_left (psi_l1 N hN α k)
        exact le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))

theorem invariant_success_bound (N k : ℕ) (hN : 0 < N) (α : ℕ → Idx N → ℝ) :
    successProbability N k α ≤ (1 / (N : ℝ)) * (sinSum N) ^ (2 * k) := by
  unfold successProbability
  have hb := successAmplitude_bound N k hN α
  calc ‖successAmplitude N k α‖ ^ 2
      ≤ (((Real.sqrt (N:ℝ))⁻¹) * (sinSum N) ^ k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = ((Real.sqrt (N:ℝ))⁻¹) ^ 2 * ((sinSum N) ^ k) ^ 2 := by ring
    _ = (1 / (N : ℝ)) * (sinSum N) ^ (2 * k) := by
        have hsq : (Real.sqrt (N:ℝ))⁻¹ ^ 2 = 1 / (N:ℝ) := by
          rw [inv_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ N), one_div]
        rw [hsq, ← pow_mul, mul_comm k 2, pow_mul]

lemma mem_oddIdx {N : ℕ} {p : Idx N} : p ∈ oddIdx N ↔ (p : ℕ) % 2 = 1 := by
  simp [oddIdx]

lemma inv_sin_le_inv_add_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ Real.pi / 2) :
    (Real.sin x)⁻¹ ≤ x⁻¹ + 1 := by
  have hsin_pos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by nlinarith [Real.pi_pos])
  have hratio : x / (1 + x) ≤ Real.sin x := by
    by_cases hx : x ≤ 3/5
    · have hcube : x - x ^ 3 / 4 < Real.sin x := by
        linarith [Real.sin_gt_sub_cube hx0, pow_nonneg hx0.le 3]
      have hden : (0:ℝ) < 1 + x := by linarith
      rw [div_le_iff₀ hden]
      have h1 : (x - x^3/4) * (1+x) ≤ Real.sin x * (1+x) :=
        mul_le_mul_of_nonneg_right hcube.le hden.le
      have hkey : 0 ≤ x^2 - x^3/4 - x^4/4 := by
        have hb : (0:ℝ) ≤ 1 - x/4 - x^2/4 := by nlinarith [sq_nonneg x, hx0, hx]
        nlinarith [mul_nonneg (sq_nonneg x) hb]
      have h2 : x ≤ (x - x^3/4) * (1+x) := by nlinarith [hkey]
      linarith
    · have hx' : 3/5 < x := not_le.mp hx
      have hmul : (2 / Real.pi) * x ≤ Real.sin x := Real.mul_le_sin hx0.le hx1
      have hden : (0:ℝ) < 1 + x := by linarith
      have hpi : Real.pi < 3.2 := Real.pi_lt_d2.trans (by norm_num)
      rw [div_le_iff₀ hden]
      have h1 : (2/Real.pi) * x * (1+x) ≤ Real.sin x * (1+x) :=
        mul_le_mul_of_nonneg_right hmul hden.le
      have hstep : x ≤ (2/Real.pi) * x * (1+x) := by
        rw [show (2/Real.pi) * x * (1+x) = (2*x*(1+x))/Real.pi by ring]
        rw [le_div_iff₀ Real.pi_pos]
        nlinarith [hx0, hx', hpi]
      linarith
  have hb : 0 < x / (1 + x) := by positivity
  have h := (inv_le_inv₀ hsin_pos hb).mpr hratio
  have heq : (x / (1 + x))⁻¹ = x⁻¹ + 1 := by
    rw [inv_div]
    field_simp
  linarith [h, heq]

lemma inv_sin_le_inv_add_inv_sub {x : ℝ} (hx0 : 0 < x) (hxπ : x < Real.pi) :
    (Real.sin x)⁻¹ ≤ x⁻¹ + (Real.pi - x)⁻¹ + 1 := by
  have hsin_pos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
  by_cases hx : x ≤ Real.pi / 2
  · have h := inv_sin_le_inv_add_one hx0 hx
    have hxpos : (0:ℝ) < x⁻¹ := inv_pos.mpr hx0
    have hsub : (0:ℝ) < Real.pi - x := by linarith [Real.pi_pos]
    have hsubpos : (0:ℝ) < (Real.pi - x)⁻¹ := inv_pos.mpr hsub
    linarith
  · have hx' : Real.pi / 2 < x := not_le.mp hx
    have hsubpos : (0:ℝ) < Real.pi - x := by linarith
    have hsubhalf : Real.pi - x ≤ Real.pi / 2 := by linarith
    have hsin : Real.sin x = Real.sin (Real.pi - x) := (Real.sin_pi_sub x).symm
    have h := inv_sin_le_inv_add_one hsubpos hsubhalf
    rw [hsin]
    have hxpos : (0:ℝ) < x⁻¹ := inv_pos.mpr hx0
    linarith

def oddbij (N : ℕ) (hN : 0 < N) (p : Idx N) : Idx N :=
  ⟨(2*N - p.val) % (2*N), Nat.mod_lt _ (by omega)⟩

lemma oddbij_val_of_mem {N : ℕ} (hN : 0 < N) {p : Idx N} (hp : p ∈ oddIdx N) :
    (oddbij N hN p).val = 2*N - p.val := by
  have h1 : p.val % 2 = 1 := mem_oddIdx.mp hp
  have hp1 : 1 ≤ p.val := by omega
  have hp2 : p.val < 2*N := p.isLt
  simp only [oddbij]
  rw [Nat.mod_eq_of_lt]
  omega

lemma oddbij_mem {N : ℕ} (hN : 0 < N) {p : Idx N} (hp : p ∈ oddIdx N) :
    oddbij N hN p ∈ oddIdx N := by
  rw [mem_oddIdx, oddbij_val_of_mem hN hp]
  have h1 : p.val % 2 = 1 := mem_oddIdx.mp hp
  obtain ⟨k, hk⟩ : ∃ k, p.val = 2*k+1 := by
    refine ⟨p.val/2, ?_⟩
    have hdm := Nat.div_add_mod p.val 2
    omega
  have h2 : p.val < 2*N := p.isLt
  have hk' : k < N := by omega
  have : 2*N - p.val = 2*(N-k-1) + 1 := by omega
  rw [this]
  omega

lemma oddbij_involutive {N : ℕ} (hN : 0 < N) {p : Idx N} (hp : p ∈ oddIdx N) :
    oddbij N hN (oddbij N hN p) = p := by
  have hp' := oddbij_mem hN hp
  apply Fin.ext
  rw [oddbij_val_of_mem hN hp', oddbij_val_of_mem hN hp]
  omega

lemma sum_oddbij {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) :
    (∑ p ∈ oddIdx N, f (2*N - p.val)) = ∑ p ∈ oddIdx N, f p.val := by
  refine Finset.sum_bij' (fun p _ => oddbij N hN p) (fun p _ => oddbij N hN p) ?_ ?_ ?_ ?_ ?_
  · exact fun p hp => oddbij_mem hN hp
  · exact fun p hp => oddbij_mem hN hp
  · exact fun p hp => oddbij_involutive hN hp
  · exact fun p hp => oddbij_involutive hN hp
  · intro p hp
    rw [oddbij_val_of_mem hN hp]

lemma test_sum {N : ℕ} (_hN : 0 < N) (f : ℕ → ℝ) :
    (∑ p ∈ oddIdx N, f p.val) = ∑ j ∈ Finset.range N, f (2*j+1) := by
  have hmem1 : ∀ p : Idx N, p ∈ oddIdx N → p.val / 2 ∈ Finset.range N := by
    intro p hp
    rw [Finset.mem_range]
    have hp2 : p.val < 2*N := p.isLt
    have hle := Nat.div_mul_le_self p.val 2
    omega
  have hmem2 : ∀ (j : ℕ) (hj : j ∈ Finset.range N), (⟨2*j+1, by
      have := Finset.mem_range.mp hj; omega⟩ : Idx N) ∈ oddIdx N := by
    intro j hj
    rw [mem_oddIdx]
    simp
  have hinv1 : ∀ (p : Idx N) (hp : p ∈ oddIdx N),
      (⟨2*(p.val/2)+1, by
        have hp2 : p.val < 2*N := p.isLt
        have := Nat.div_mul_le_self p.val 2
        omega⟩ : Idx N) = p := by
    intro p hp
    apply Fin.ext
    show 2*(p.val/2)+1 = p.val
    have h1 : p.val % 2 = 1 := mem_oddIdx.mp hp
    have hdm := Nat.div_add_mod p.val 2
    rw [h1] at hdm
    omega
  have hinv2 : ∀ (j : ℕ) (hj : j ∈ Finset.range N), (2*j+1)/2 = j := by
    intro j hj
    have hdm := Nat.div_add_mod (2*j+1) 2
    have hmod : (2*j+1) % 2 = 1 := by omega
    rw [hmod] at hdm
    omega
  have hval : ∀ (p : Idx N) (hp : p ∈ oddIdx N), f p.val = f (2*(p.val/2)+1) := by
    intro p hp
    congr 1
    have h1 : p.val % 2 = 1 := mem_oddIdx.mp hp
    have hdm := Nat.div_add_mod p.val 2
    rw [h1] at hdm
    omega
  exact Finset.sum_bij' (fun p _ => p.val/2) (fun (j : ℕ) (hj : j ∈ Finset.range N) =>
      (⟨2*j+1, by have := Finset.mem_range.mp hj; omega⟩ : Idx N)) hmem1 hmem2 hinv1 hinv2 hval

lemma odd_harm_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range m, ((2*(j:ℝ)+1))⁻¹ ≤ 1 + (1/2) * Real.log (2*(m:ℝ)-1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [Finset.sum_range_succ]
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      have hmpos : (0:ℝ) < (m:ℝ) := by linarith
      have hA : (0:ℝ) < 2*(m:ℝ)-1 := by linarith
      have hB : (0:ℝ) < 2*(m:ℝ)+1 := by linarith
      have hterm : ((2*(m:ℝ)+1))⁻¹ ≤
          (1/2) * (Real.log (2*(m:ℝ)+1) - Real.log (2*(m:ℝ)-1)) := by
        have ht : (0:ℝ) ≤ 2/(2*(m:ℝ)-1) := by positivity
        have hlog := Real.le_log_one_add_of_nonneg ht
        have heq : 2 * (2/(2*(m:ℝ)-1)) / (2/(2*(m:ℝ)-1) + 2) = 1/(m:ℝ) := by
          field_simp
          ring
        have hratio : 1 + 2/(2*(m:ℝ)-1) = (2*(m:ℝ)+1)/(2*(m:ℝ)-1) := by
          field_simp
          ring
        rw [heq, hratio] at hlog
        rw [Real.log_div (ne_of_gt hB) (ne_of_gt hA)] at hlog
        have hcmp : ((2*(m:ℝ)+1))⁻¹ ≤ (1:ℝ)/(2*(m:ℝ)) := by
          have h2m : (0:ℝ) < 2*(m:ℝ) := by linarith
          have hle : 2*(m:ℝ) ≤ 2*(m:ℝ)+1 := by linarith
          have := one_div_le_one_div_of_le h2m hle
          simpa [one_div] using this
        have hhalf : (1:ℝ)/(2*(m:ℝ)) = (1/2)*(1/(m:ℝ)) := by
          field_simp
        have := mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 1/2)
        rw [hhalf] at hcmp
        linarith
      push_cast
      have hgoal : 1 + (1/2) * Real.log (2*((m:ℝ)+1)-1) =
          1 + (1/2) * Real.log (2*(m:ℝ)+1) := by
        rw [show 2*((m:ℝ)+1)-1 = 2*(m:ℝ)+1 by ring]
      rw [hgoal]
      linarith

lemma oddIdx_card_le (N : ℕ) : (oddIdx N).card ≤ 2 * N := by
  have h :=
      Finset.card_le_card (Finset.filter_subset (fun p : Idx N => (p : ℕ) % 2 = 1) Finset.univ)
  simpa [oddIdx, Idx] using h

theorem sinSum_le_log (N : ℕ) (hN : 1 ≤ N) :
    sinSum N ≤ (2 / Real.pi) * Real.log (N : ℝ) + 4 := by
  have hNpos : 0 < N := hN
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hterm : ∀ p ∈ oddIdx N,
      (Real.sin (Real.pi * (p:ℝ) / (2*(N:ℝ))))⁻¹ ≤
        (2*(N:ℝ))/(Real.pi*(p:ℝ)) + (2*(N:ℝ))/(Real.pi*(2*(N:ℝ)-(p:ℝ))) + 1 := by
    intro p hp
    have hp1 : 1 ≤ p.val := by
      have := mem_oddIdx.mp hp; omega
    have hp2 : p.val < 2*N := p.isLt
    set x := Real.pi * (p:ℝ) / (2*(N:ℝ)) with hxdef
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hp1)
    have h2NR : (0:ℝ) < 2*(N:ℝ) := by positivity
    have hx0 : 0 < x := by
      rw [hxdef]; positivity
    have hxπ : x < Real.pi := by
      rw [hxdef, div_lt_iff₀ h2NR]
      have : (p:ℝ) < 2*(N:ℝ) := by exact_mod_cast hp2
      nlinarith [Real.pi_pos]
    have h := inv_sin_le_inv_add_inv_sub hx0 hxπ
    have hsub : (0:ℝ) < 2*(N:ℝ) - (p:ℝ) := by
      have : (p:ℝ) < 2*(N:ℝ) := by exact_mod_cast hp2
      linarith
    have hx1 : x⁻¹ = (2*(N:ℝ))/(Real.pi*(p:ℝ)) := by
      rw [hxdef]; field_simp
    have hx2 : (Real.pi - x)⁻¹ = (2*(N:ℝ))/(Real.pi*(2*(N:ℝ)-(p:ℝ))) := by
      rw [hxdef]; field_simp
    rw [hx1, hx2] at h
    exact h
  set A : ℝ := ∑ p ∈ oddIdx N, ((p:ℝ))⁻¹ with hAdef
  have hS1 : (∑ p ∈ oddIdx N, (2*(N:ℝ))/(Real.pi*(p:ℝ))) = (2*(N:ℝ)/Real.pi) * A := by
    rw [hAdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : 1 ≤ p.val := by have := mem_oddIdx.mp hp; omega
    have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hp1)
    field_simp
  have hS2 : (∑ p ∈ oddIdx N, (2*(N:ℝ))/(Real.pi*(2*(N:ℝ)-(p:ℝ)))) = (2*(N:ℝ)/Real.pi) * A := by
    rw [hAdef, Finset.mul_sum]
    have hterm2 : ∀ p ∈ oddIdx N,
        (2*(N:ℝ))/(Real.pi*(2*(N:ℝ)-(p:ℝ))) =
          (2*(N:ℝ)/Real.pi) * (((2*N - p.val : ℕ) : ℝ))⁻¹ := by
      intro p hp
      have hp2 : p.val < 2*N := p.isLt
      have hcast : ((2*N - p.val : ℕ) : ℝ) = 2*(N:ℝ) - (p:ℝ) := by
        rw [Nat.cast_sub (le_of_lt hp2)]
        push_cast
        ring
      rw [hcast]
      have hsub : (0:ℝ) < 2*(N:ℝ) - (p:ℝ) := by
        have : (p:ℝ) < 2*(N:ℝ) := by exact_mod_cast hp2
        linarith
      field_simp
    rw [Finset.sum_congr rfl hterm2]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    exact sum_oddbij hNpos (fun q => (q:ℝ)⁻¹)
  have hS3 : (∑ p ∈ oddIdx N, (1:ℝ)) = ((oddIdx N).card : ℝ) := by simp
  have hRHS : (∑ p ∈ oddIdx N,
        ((2*(N:ℝ))/(Real.pi*(p:ℝ)) + (2*(N:ℝ))/(Real.pi*(2*(N:ℝ)-(p:ℝ))) + 1))
      = 2 * ((2*(N:ℝ)/Real.pi) * A) + ((oddIdx N).card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hS1, hS2, hS3]
    ring
  have hbound : (∑ p ∈ oddIdx N, (Real.sin (Real.pi * (p:ℝ) / (2*(N:ℝ))))⁻¹)
      ≤ 2 * ((2*(N:ℝ)/Real.pi) * A) + ((oddIdx N).card : ℝ) := by
    rw [← hRHS]
    exact Finset.sum_le_sum hterm
  have hAeq : A ≤ 1 + (1/2)*Real.log (2*(N:ℝ)-1) := by
    rw [hAdef]
    rw [test_sum hNpos (fun q => ((q:ℝ))⁻¹)]
    have h := odd_harm_le N hN
    simpa using h
  have hfinal : sinSum N ≤ (1/(N:ℝ)) *
      (2 * ((2*(N:ℝ)/Real.pi) * A) + ((oddIdx N).card : ℝ)) := by
    unfold sinSum
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have hposc : (0:ℝ) ≤ 2*(N:ℝ)/Real.pi := by positivity
  have hc : ((oddIdx N).card : ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast oddIdx_card_le N
  have hstep1 : (1/(N:ℝ)) * (2 * ((2*(N:ℝ)/Real.pi) * A) + ((oddIdx N).card : ℝ))
      ≤ (1/(N:ℝ)) * (2 * ((2*(N:ℝ)/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1))) + 2*(N:ℝ)) := by
    have h1 : (2*(N:ℝ)/Real.pi) * A ≤ (2*(N:ℝ)/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hAeq hposc
    have h2 :
        2 * ((2*(N:ℝ)/Real.pi) * A) ≤ 2 * ((2*(N:ℝ)/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1))) :=
        by linarith
    have h3 : 2 * ((2*(N:ℝ)/Real.pi) * A) + ((oddIdx N).card : ℝ)
        ≤ 2 * ((2*(N:ℝ)/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1))) + 2*(N:ℝ) := by linarith
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hlogbound : Real.log (2*(N:ℝ)-1) ≤ Real.log 2 + Real.log (N:ℝ) := by
    have hpos1 : (0:ℝ) < 2*(N:ℝ)-1 := by
      have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith
    have hle : 2*(N:ℝ)-1 ≤ 2*(N:ℝ) := by linarith
    have hmono : Real.log (2*(N:ℝ)-1) ≤ Real.log (2*(N:ℝ)) := Real.log_le_log hpos1 hle
    have hdecomp : Real.log (2*(N:ℝ)) = Real.log 2 + Real.log (N:ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hNR)]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have heq : (1/(N:ℝ)) * (2 * ((2*(N:ℝ)/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1))) + 2*(N:ℝ))
      = (4/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1)) + 2 := by
    field_simp
    ring
  have hconst : (4/Real.pi) + (2/Real.pi) * Real.log 2 + 2 ≤ 4 := by
    have hpos : (0:ℝ) < Real.pi := Real.pi_pos
    have hkey : 4 + 2*Real.log 2 ≤ 2*Real.pi := by
      have h3 : (3:ℝ) < Real.pi := Real.pi_gt_three
      linarith
    have hdiv : (4 + 2*Real.log 2)/Real.pi ≤ 2 := by
      rw [div_le_iff₀ hpos]; linarith
    have he : (4/Real.pi) + (2/Real.pi) * Real.log 2 = (4 + 2*Real.log 2)/Real.pi := by
      field_simp
    linarith [he, hdiv]
  calc sinSum N ≤ (1/(N:ℝ)) * (2 * ((2*(N:ℝ)/Real.pi) * A) + ((oddIdx N).card : ℝ)) := hfinal
    _ ≤ (1/(N:ℝ)) * (2 * ((2*(N:ℝ)/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1))) + 2*(N:ℝ)) := hstep1
    _ = (4/Real.pi) * (1 + (1/2)*Real.log (2*(N:ℝ)-1)) + 2 := heq
    _ = (4/Real.pi) + (2/Real.pi) * Real.log (2*(N:ℝ)-1) + 2 := by
        field_simp
        ring
    _ ≤ (2/Real.pi) * Real.log (N:ℝ) + 4 := by
        have hstep : (2/Real.pi) * Real.log (2*(N:ℝ)-1) ≤ (2/Real.pi) * (Real.log 2 + Real.log (N:ℝ)) :=
          mul_le_mul_of_nonneg_left hlogbound (by positivity)
        nlinarith [hstep, hconst]

theorem odd_sine_sum_asymptotic :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N → sinSum N ≤ (2 / Real.pi) * Real.log (N : ℝ) + C :=
  ⟨4, by norm_num, fun N hN => sinSum_le_log N (by omega)⟩

theorem translation_invariant_query_lower_bound (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ,
      (∃ α : ℕ → Idx N → ℝ, ε ≤ successProbability N k α) →
      Real.log (N : ℝ) / (2 * Real.log (Real.log (N : ℝ))) < (k : ℝ) := by
  set c : ℝ := -Real.log ε with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    have := Real.log_nonpos (le_of_lt hε0) hε1
    linarith
  have hexp : Real.exp (-c) = ε := by
    have h1 : -c = Real.log ε := by rw [hcdef]; ring
    rw [h1, Real.exp_log hε0]
  refine ⟨Nat.ceil (Real.exp (max 17 (4096 * (c + 1) ^ 2))) + 1, ?_⟩
  intro N hN k hk
  obtain ⟨α, hα⟩ := hk
  have hMge : Real.exp (max 17 (4096 * (c + 1) ^ 2)) ≤ (N : ℝ) := by
    have h1 : Nat.ceil (Real.exp (max 17 (4096 * (c + 1) ^ 2))) ≤ N := by omega
    have h2 : (Nat.ceil (Real.exp (max 17 (4096 * (c + 1) ^ 2))) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast h1
    have h3 : Real.exp (max 17 (4096 * (c + 1) ^ 2)) ≤
        (Nat.ceil (Real.exp (max 17 (4096 * (c + 1) ^ 2))) : ℝ) := Nat.le_ceil _
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hMge
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hN1 : 1 ≤ N := hNnat
  have hLge : max 17 (4096 * (c + 1) ^ 2) ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hMge
    rwa [Real.log_exp] at h
  have hL17 : 17 ≤ Real.log (N : ℝ) := le_trans (le_max_left _ _) hLge
  have hLc : 4096 * (c + 1) ^ 2 ≤ Real.log (N : ℝ) := le_trans (le_max_right _ _) hLge
  have hLpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  have hlogLpos : (0 : ℝ) < Real.log (Real.log (N : ℝ)) := by
    apply Real.log_pos; linarith
  have hlogbig : (1 / 16 : ℝ) < Real.log (Real.log (N : ℝ)) := by
    have hlog17 : Real.log 17 ≤ Real.log (Real.log (N : ℝ)) := Real.log_le_log (by norm_num) hL17
    have hlt : (1 / 16 : ℝ) < Real.log 17 := by
      have hexp : Real.exp (1 / 16) < 17 := by
        have h1 : Real.exp (1 / 16) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
        have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      have h := Real.log_lt_log (Real.exp_pos (1 / 16)) hexp
      rwa [Real.log_exp] at h
    linarith
  have hS_le : sinSum N ≤ (2 / Real.pi) * Real.log (N : ℝ) + 4 := sinSum_le_log N hN1
  have hb := invariant_success_bound N k hNnat α
  have hεS : ε ≤ (1 / (N : ℝ)) * (sinSum N) ^ (2 * k) := le_trans hα hb
  have hεN_le : ε * (N : ℝ) ≤ (sinSum N) ^ (2 * k) := by
    have h := mul_le_mul_of_nonneg_right hεS hNpos.le
    have hcancel : (1 / (N : ℝ) * (sinSum N) ^ (2 * k)) * (N : ℝ) = (sinSum N) ^ (2 * k) := by
      field_simp
    linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exfalso
    have h1 : ε * (N : ℝ) ≤ 1 := by
      have := hεN_le; rw [hk0] at this; simpa using this
    have hgt : 1 < ε * (N : ℝ) := by
      have hle2 : Real.exp (-c) * Real.exp (max 17 (4096 * (c + 1) ^ 2)) ≤ ε * (N : ℝ) :=
        mul_le_mul hexp.le hMge (Real.exp_pos _).le hε0.le
      have hgt2 : 1 < Real.exp (-c) * Real.exp (max 17 (4096 * (c + 1) ^ 2)) := by
        rw [← Real.exp_add]
        apply Real.one_lt_exp_iff.mpr
        have hcM : c < max 17 (4096 * (c + 1) ^ 2) := by
          have hbig : c < 4096 * (c + 1) ^ 2 := by nlinarith [sq_nonneg (c + 1), hc0]
          exact lt_of_lt_of_le hbig (le_max_right _ _)
        linarith
      linarith
    linarith
  · have hS0 : 0 < sinSum N := by
      rcases lt_or_ge 0 (sinSum N) with h | h
      · exact h
      · exfalso
        have hzero : sinSum N = 0 := le_antisymm h (sinSum_nonneg N hNnat)
        have hp : (sinSum N) ^ (2 * k) = 0 := by
          rw [hzero]; exact zero_pow (by omega)
        have := mul_pos hε0 hNpos
        linarith
    have hlog1 : Real.log (ε * (N : ℝ)) ≤ Real.log ((sinSum N) ^ (2 * k)) :=
      Real.log_le_log (mul_pos hε0 hNpos) hεN_le
    have hlogεN : Real.log (ε * (N : ℝ)) = -c + Real.log (N : ℝ) := by
      rw [Real.log_mul (ne_of_gt hε0) (ne_of_gt hNpos), hcdef]; ring
    have hlogpow : Real.log ((sinSum N) ^ (2 * k)) = (2 * (k : ℝ)) * Real.log (sinSum N) := by
      rw [Real.log_pow]; push_cast; ring
    have hSlog : Real.log (sinSum N) ≤ Real.log (Real.log (N : ℝ)) - 1 / 16 := by
      have hstep1 : Real.log (sinSum N) ≤ Real.log ((2 / Real.pi) * Real.log (N : ℝ) + 4) :=
        Real.log_le_log hS0 hS_le
      have hXpos : (0 : ℝ) < 2 / Real.pi + 4 / Real.log (N : ℝ) := by
        apply add_pos
        · positivity
        · exact div_pos (by norm_num) hLpos
      have hsplit : Real.log ((2 / Real.pi) * Real.log (N : ℝ) + 4) =
          Real.log (Real.log (N : ℝ)) + Real.log (2 / Real.pi + 4 / Real.log (N : ℝ)) := by
        have heq2 : (2 / Real.pi) * Real.log (N : ℝ) + 4 =
            Real.log (N : ℝ) * (2 / Real.pi + 4 / Real.log (N : ℝ)) := by
          field_simp
        rw [heq2, Real.log_mul (ne_of_gt hLpos) (ne_of_gt hXpos)]
      have hratio_le : 2 / Real.pi + 4 / Real.log (N : ℝ) ≤ 15 / 16 := by
        have h4 : 4 / Real.log (N : ℝ) ≤ 4 / 17 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL17
        have hpi2 : 2 / Real.pi ≤ 2 / 3 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
          rw [show (2:ℝ) / Real.pi * 3 = 6 / Real.pi by ring]
          rw [div_le_iff₀ Real.pi_pos]
          nlinarith [Real.pi_gt_three]
        linarith
      have hlogratio : Real.log (2 / Real.pi + 4 / Real.log (N : ℝ)) ≤ -1 / 16 := by
        have := Real.log_le_sub_one_of_pos hXpos
        linarith
      linarith [hstep1, hsplit, hlogratio]
    have hsqrt : 64 * (c + 1) ≤ Real.sqrt (Real.log (N : ℝ)) := by
      have h1 : Real.sqrt (4096 * (c + 1) ^ 2) ≤ Real.sqrt (Real.log (N : ℝ)) :=
        Real.sqrt_le_sqrt hLc
      have h2 : Real.sqrt (4096 * (c + 1) ^ 2) = 64 * (c + 1) := by
        rw [show (4096 : ℝ) * (c + 1) ^ 2 = 64 ^ 2 * (c + 1) ^ 2 by norm_num]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64 ^ 2)]
        rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 64),
            Real.sqrt_sq (by linarith : (0 : ℝ) ≤ c + 1)]
      linarith
    have hlogL_le : Real.log (Real.log (N : ℝ)) ≤ 2 * Real.sqrt (Real.log (N : ℝ)) := by
      have h1 : Real.log (Real.log (N : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (N : ℝ))) := by
        conv_lhs => rw [← Real.sq_sqrt hLpos.le]
        rw [Real.log_pow]; push_cast; ring
      rw [h1]
      have h2 : Real.log (Real.sqrt (Real.log (N : ℝ))) ≤ Real.sqrt (Real.log (N : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
      have h3 : (0 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
      linarith
    have hclogL : c * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) / 16 := by
      have h1 : c * Real.log (Real.log (N : ℝ)) ≤ c * (2 * Real.sqrt (Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogL_le hc0
      have hspos : (0 : ℝ) < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hLpos
      have h32 : 32 * c < Real.sqrt (Real.log (N : ℝ)) := by linarith
      have h2 : 32 * c * Real.sqrt (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
        have h := mul_lt_mul_of_pos_right h32 hspos
        have hsq2 : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) = Real.log (N : ℝ) := by
          rw [← sq, Real.sq_sqrt hLpos.le]
        linarith [h, hsq2]
      linarith
    have hmain : (Real.log (N : ℝ) - c) / (2 * (Real.log (Real.log (N : ℝ)) - 1 / 16)) ≤ (k : ℝ) := by
      have h1 : -c + Real.log (N : ℝ) ≤ (2 * (k : ℝ)) * Real.log (sinSum N) := by
        have := hlog1
        rw [hlogεN, hlogpow] at this
        linarith
      have h2 : (2 * (k : ℝ)) * Real.log (sinSum N) ≤
          (2 * (k : ℝ)) * (Real.log (Real.log (N : ℝ)) - 1 / 16) :=
        mul_le_mul_of_nonneg_left hSlog (by positivity)
      have h3 := le_trans h1 h2
      have hden : (0 : ℝ) < 2 * (Real.log (Real.log (N : ℝ)) - 1 / 16) := by linarith [hlogbig]
      rw [div_le_iff₀ hden]
      linarith
    have hAcmp : Real.log (N : ℝ) / (2 * Real.log (Real.log (N : ℝ))) <
        (Real.log (N : ℝ) - c) / (2 * (Real.log (Real.log (N : ℝ)) - 1 / 16)) := by
      have hden1 : (0 : ℝ) < 2 * Real.log (Real.log (N : ℝ)) := by linarith
      have hden2 : (0 : ℝ) < 2 * (Real.log (Real.log (N : ℝ)) - 1 / 16) := by linarith [hlogbig]
      rw [div_lt_div_iff₀ hden1 hden2]
      nlinarith [hclogL]
    linarith

end Qatlib.Papers.OrderedInsert99.MainResults
