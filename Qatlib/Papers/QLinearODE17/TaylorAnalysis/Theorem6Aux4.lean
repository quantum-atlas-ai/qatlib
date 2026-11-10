/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6Aux3
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

theorem taylorPoly_zero (k : ℕ) : taylorPoly k 0 = 1 := by
  rw [taylorPoly, Finset.sum_range_succ']
  simp

theorem taylorSrcPoly_zero {k : ℕ} (hk : 1 ≤ k) : taylorSrcPoly k 0 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [taylorSrcPoly, Finset.sum_range_succ']
  simp

noncomputable def duhamelCoord (lam yv βv : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (lam * t) * (yv + ∫ s in 0..t, Complex.exp (-(lam * s)) * βv)

theorem duhamelCoord_zero (lam yv βv : ℂ) : duhamelCoord lam yv βv 0 = yv := by
  simp [duhamelCoord]

theorem duhamelCoord_of_lam_zero {lam yv βv : ℂ} (hlam : lam = 0) (t : ℝ) :
    duhamelCoord lam yv βv t = yv + t * βv := by
  subst hlam
  simp only [duhamelCoord, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_const]
  simp

theorem duhamelCoord_step_lam_zero {lam yv βv : ℂ} (hlam : lam = 0) (h τ : ℝ) :
    duhamelCoord lam yv βv (τ + h) = duhamelCoord lam yv βv τ + h * βv := by
  rw [duhamelCoord_of_lam_zero hlam, duhamelCoord_of_lam_zero hlam]
  push_cast
  ring

theorem duhamelCoord_step {lam yv βv : ℂ} {h τ : ℝ} (hlam : lam ≠ 0) :
    duhamelCoord lam yv βv (τ + h) =
      Complex.exp (lam * h) * duhamelCoord lam yv βv τ
        + βv * (Complex.exp (lam * h) - 1) / lam := by
  have hint : ∀ (a b : ℝ), IntervalIntegrable (fun s : ℝ => Complex.exp (-(lam * ↑s)) * βv)
      MeasureTheory.volume a b := fun a b =>
    (by continuity : Continuous _).intervalIntegrable a b
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(lam * ↑s)))
      (Complex.exp (-(lam * ↑s)) * (-(lam * (1 : ℂ)))) s := by
    intro s
    have h0 : HasDerivAt (fun s : ℝ => (-(lam : ℂ)) • (↑s : ℂ)) ((-(lam : ℂ)) • (1 : ℂ)) s :=
      (Complex.ofRealCLM.hasDerivAt (x := s)).const_smul (-(lam : ℂ))
    simpa only [smul_eq_mul, neg_mul] using! h0.cexp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := τ) (b := τ + h)
    (f := fun s : ℝ => Complex.exp (-(lam * ↑s)))
    (f' := fun s : ℝ => Complex.exp (-(lam * ↑s)) * (-(lam * (1 : ℂ))))
    (fun s _ => hderiv s)
    ((by continuity : Continuous (fun s : ℝ =>
      Complex.exp (-(lam * ↑s)) * (-(lam * (1 : ℂ))))).intervalIntegrable τ (τ + h))
  have hkey : (∫ s in τ..τ + h, Complex.exp (-(lam * ↑s))) * (-(lam * (1 : ℂ)))
      = Complex.exp (-(lam * ↑(τ + h))) - Complex.exp (-(lam * ↑τ)) := by
    rw [← intervalIntegral.integral_mul_const, hftc]
  have hlamI : (∫ s in τ..τ + h, Complex.exp (-(lam * ↑s))) * (lam * (1 : ℂ))
      = Complex.exp (-(lam * ↑τ)) - Complex.exp (-(lam * ↑(τ + h))) := by
    linear_combination -hkey
  have hmid : ∫ s in τ..τ + h, Complex.exp (-(lam * ↑s)) * βv
      = βv * (Complex.exp (-(lam * ↑τ)) - Complex.exp (-(lam * ↑(τ + h)))) / lam := by
    rw [intervalIntegral.integral_mul_const, ← hlamI]
    field_simp
  have hE : Complex.exp (lam * ↑(τ + h)) = Complex.exp (lam * ↑τ) * Complex.exp (lam * ↑h) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc1 : Complex.exp (lam * ↑τ) * Complex.exp (-(lam * ↑τ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hc2 : Complex.exp (lam * ↑τ) * Complex.exp (lam * ↑h)
      * Complex.exp (-(lam * ↑(τ + h))) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    have hz : (lam * ↑τ + lam * ↑h) + -(lam * ↑(τ + h)) = 0 := by
      push_cast
      ring
    rw [hz, Complex.exp_zero]
  have hd : Complex.exp (lam * ↑τ) * Complex.exp (lam * ↑h) *
        (Complex.exp (-(lam * ↑τ)) - Complex.exp (-(lam * ↑(τ + h))))
      = Complex.exp (lam * ↑h) - 1 := by
    rw [mul_sub,
      show Complex.exp (lam * ↑τ) * Complex.exp (lam * ↑h) * Complex.exp (-(lam * ↑τ))
        = Complex.exp (lam * ↑τ) * Complex.exp (-(lam * ↑τ)) * Complex.exp (lam * ↑h) from by
        ring, hc1, one_mul, hc2]
  simp only [duhamelCoord,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ (τ + h)), hmid, hE]
  linear_combination (βv * lam⁻¹) * hd

theorem duhamelCoord_norm_le (lam yv βv : ℂ) (hre : lam.re ≤ 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖duhamelCoord lam yv βv t‖ ≤ ‖yv‖ + t * ‖βv‖ := by
  have hint : IntervalIntegrable (fun s : ℝ => Complex.exp (-(lam * ↑s)) * βv)
      MeasureTheory.volume 0 t :=
    (by continuity : Continuous _).intervalIntegrable 0 t
  have hexpneg : ∀ s : ℝ, Complex.exp (lam * ↑t) * (Complex.exp (-(lam * ↑s)) * βv)
      = Complex.exp (lam * ↑(t - s)) * βv := by
    intro s
    have h1 : Complex.exp (lam * ↑t) * Complex.exp (-(lam * ↑s)) = Complex.exp (lam * ↑(t - s)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [show Complex.exp (lam * ↑t) * (Complex.exp (-(lam * ↑s)) * βv)
          = (Complex.exp (lam * ↑t) * Complex.exp (-(lam * ↑s))) * βv from by ring, h1]
  have hsplit2 : ∫ s in 0..t, Complex.exp (lam * ↑t) * (Complex.exp (-(lam * ↑s)) * βv)
      = Complex.exp (lam * ↑t) * ∫ s in 0..t, Complex.exp (-(lam * ↑s)) * βv :=
    intervalIntegral.integral_const_mul (𝕜 := ℂ) (Complex.exp (lam * ↑t))
      (fun s : ℝ => Complex.exp (-(lam * ↑s)) * βv)
  have hspl : duhamelCoord lam yv βv t = Complex.exp (lam * ↑t) * yv
      + ∫ s in 0..t, Complex.exp (lam * ↑(t - s)) * βv := by
    simp only [duhamelCoord, mul_add, ← hsplit2]
    congr 1
    exact intervalIntegral.integral_congr fun s _ => hexpneg s
  have hb1 : ‖Complex.exp (lam * ↑t) * yv‖ ≤ ‖yv‖ := by
    have hle1 : ‖Complex.exp (lam * ↑t)‖ ≤ 1 := by
      have hre' : (lam * ↑t).re ≤ 0 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg hre ht
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hre'
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg yv) hle1
  have hb2 : ‖∫ s in 0..t, Complex.exp (lam * ↑(t - s)) * βv‖ ≤ t * ‖βv‖ := by
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖Complex.exp (lam * ↑(t - s)) * βv‖ ≤ ‖βv‖ := by
      intro s hs
      rw [Set.uIoc_of_le ht] at hs
      have hs2 : s ≤ t := hs.2
      have hts : (0 : ℝ) ≤ t - s := by linarith
      have hle1 : ‖Complex.exp (lam * ↑(t - s))‖ ≤ 1 := by
        have hre' : (lam * ↑(t - s)).re ≤ 0 := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          exact mul_nonpos_of_nonpos_of_nonneg hre hts
        rw [Complex.norm_exp]
        exact Real.exp_le_one_iff.mpr hre'
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg βv) hle1
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rwa [sub_zero, abs_of_nonneg ht, mul_comm] at hle
  rw [hspl]
  exact (norm_add_le _ _).trans (by linarith [hb1, hb2])

theorem exp_seven_twelfths_le : Real.exp (7 / 12 : ℝ) ≤ 12 / 5 := by
  have h1 : (5 / 12 : ℝ) ≤ Real.exp (-(7 / 12 : ℝ)) := by
    have h2 := Real.add_one_le_exp (-(7 / 12 : ℝ))
    linarith
  have h2 : Real.exp (7 / 12 : ℝ) = (Real.exp (-(7 / 12 : ℝ)))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [h2]
  calc (Real.exp (-(7 / 12 : ℝ)))⁻¹ ≤ (5 / 12 : ℝ)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 5 / 12)).mpr h1
    _ = 12 / 5 := by norm_num

theorem scalar_gronwall (m : ℕ) (_hm : 0 < m) (F : ℝ) (hF0 : 0 < F) (hFm : (2 * m : ℝ) ≤ F)
    (u v : ℝ) (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (E Φ : ℕ → ℝ) (hE0 : E 0 = 0) (_hEnn : ∀ j, 0 ≤ E j)
    (_hΦnn : ∀ j, 0 ≤ Φ j) (hΦ : ∀ j, Φ j ≤ u + (j : ℝ) * v)
    (hstep : ∀ j : ℕ, (j : ℝ) ≤ (m : ℝ) →
      E (j + 1) ≤ (1 + (7 / 6 : ℝ) / F) * E j + (7 / 6 : ℝ) / F * Φ j + (7 / 6 : ℝ) / F * v)
    (j : ℕ) (hjm : (j : ℝ) ≤ (m : ℝ)) :
    E j ≤ 2.8 * (j : ℝ) * (u + (m : ℝ) * v) / F := by
  set δ : ℝ := (7 / 6) / F with hδ
  have hδnn : 0 ≤ δ := by positivity
  have hF2 : (m : ℝ) ≤ F / 2 := by linarith
  have hpow : ∀ c : ℕ, (c : ℝ) ≤ (m : ℝ) → (1 + δ) ^ c ≤ 12 / 5 := by
    intro c hc
    have hle : (1 + δ) ≤ Real.exp δ := by
      have h2 := Real.add_one_le_exp δ
      linarith
    have h1 : (1 + δ) ^ c ≤ (Real.exp δ) ^ c :=
      pow_le_pow_left₀ (by linarith) hle c
    have h2 : (Real.exp δ) ^ c = Real.exp (δ * (c : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h3 : δ * (c : ℝ) ≤ 7 / 12 := by
      have hca : δ * (c : ℝ) ≤ δ * (m : ℝ) := mul_le_mul_of_nonneg_left hc hδnn
      have hcb : δ * (m : ℝ) ≤ 7 / 12 := by
        have hma : (m : ℝ) / F ≤ 1 / 2 := by
          rw [div_le_iff₀ hF0]
          linarith
        have hmb : δ * (m : ℝ) = (7 / 6) * ((m : ℝ) / F) := by
          rw [hδ, div_mul_eq_mul_div, div_eq_mul_inv]
          ring
        rw [hmb]
        nlinarith
      linarith
    calc (1 + δ) ^ c ≤ (Real.exp δ) ^ c := h1
      _ = Real.exp (δ * (c : ℝ)) := h2
      _ ≤ Real.exp (7 / 12) := Real.exp_le_exp.mpr h3
      _ ≤ 12 / 5 := exp_seven_twelfths_le
  have hexpansion : ∀ (j : ℕ), (j : ℝ) ≤ (m : ℝ) →
      E j ≤ ∑ b ∈ Finset.range j, (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v) := by
    intro j
    induction j with
    | zero => simp [hE0]
    | succ j ih =>
      intro hjm
      have hjm' : (j : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.le_of_succ_le (by exact_mod_cast hjm : j + 1 ≤ m)
      have hs := hstep j hjm'
      have hih := ih hjm'
      have hj0 : j + 1 - 1 - j = 0 := by omega
      rw [Finset.sum_range_succ, hj0, pow_zero, one_mul]
      have hsum : ∑ b ∈ Finset.range j, (1 + δ) ^ (j + 1 - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v)
          = (1 + δ) * ∑ b ∈ Finset.range j,
              (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b hb => ?_
        have hbj : b < j := Finset.mem_range.mp hb
        have hidx : j + 1 - 1 - b = (j - 1 - b) + 1 := by omega
        rw [hidx, pow_succ]
        ring
      have hΦj := hΦ j
      have h1 : (1 + δ) * E j ≤ (1 + δ) * ∑ b ∈ Finset.range j,
          (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v) :=
        mul_le_mul_of_nonneg_left hih (by linarith)
      have h2 : δ * Φ j ≤ δ * (u + (j : ℝ) * v) := mul_le_mul_of_nonneg_left hΦj hδnn
      rw [hsum]
      linarith
  have hjm_nat : j ≤ m := by exact_mod_cast hjm
  have hsumbound : ∑ b ∈ Finset.range j, (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v)
      ≤ (12 / 5) * ((7 / 6 : ℝ) / F) * ((j : ℝ) * (u + (m : ℝ) * v)) := by
    have h125 : (0 : ℝ) ≤ 12 / 5 := by norm_num
    have htermle : ∀ b ∈ Finset.range j,
        (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v)
        ≤ (12 / 5) * (δ * (u + (m : ℝ) * v)) := by
      intro b hb
      have hbj : b < j := Finset.mem_range.mp hb
      have hcm : ((j - 1 - b : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega)
      have hp := hpow (j - 1 - b) hcm
      have hb1m : (b : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega)
      have hvv : (b : ℝ) * v + v ≤ (m : ℝ) * v := by
        have hrew : (b : ℝ) * v + v = ((b : ℝ) + 1) * v := by ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_right hb1m hv
      have hinner : δ * (u + (b : ℝ) * v) + δ * v ≤ δ * (u + (m : ℝ) * v) := by
        have hsplit : δ * (u + (b : ℝ) * v) + δ * v = δ * ((u + (b : ℝ) * v) + v) := by ring
        rw [hsplit]
        refine mul_le_mul_of_nonneg_left ?_ hδnn
        linarith
      have hpos : 0 ≤ δ * (u + (b : ℝ) * v) + δ * v := by
        have hle1 : 0 ≤ δ * (u + (b : ℝ) * v) + δ * v :=
          calc 0 ≤ δ * (u + (b : ℝ) * v) := by positivity
            _ ≤ δ * (u + (b : ℝ) * v) + δ * v :=
              le_add_of_nonneg_right (show 0 ≤ δ * v by positivity)
        exact hle1
      calc (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v)
          ≤ (12 / 5) * (δ * (u + (b : ℝ) * v) + δ * v) :=
            mul_le_mul_of_nonneg_right hp hpos
        _ ≤ (12 / 5) * (δ * (u + (m : ℝ) * v)) :=
            mul_le_mul_of_nonneg_left hinner h125
    have hsumle : ∑ b ∈ Finset.range j, (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v)
        ≤ ∑ _b ∈ Finset.range j, (12 / 5) * (δ * (u + (m : ℝ) * v)) :=
      Finset.sum_le_sum htermle
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsumle
    refine hsumle.trans_eq ?_
    rw [hδ]
    ring
  calc E j ≤ ∑ b ∈ Finset.range j,
        (1 + δ) ^ (j - 1 - b) * (δ * (u + (b : ℝ) * v) + δ * v) := hexpansion j hjm
    _ ≤ (12 / 5) * ((7 / 6 : ℝ) / F) * ((j : ℝ) * (u + (m : ℝ) * v)) := hsumbound
    _ = 2.8 * (j : ℝ) * (u + (m : ℝ) * v) / F := by ring

section Evolution

variable {N : Type} [Fintype N] [DecidableEq N]

noncomputable def conjSeq (k : ℕ) (h : ℝ) (D : Matrix N N ℂ) (y βc : QState N) :
    ℕ → QState N
  | 0 => y
  | j + 1 => fun n => taylorPoly k (↑h * D n n) * conjSeq k h D y βc j n
      + ↑h * βc n * taylorSrcPoly k (↑h * D n n)

theorem taylorV2_block_evolution (m k p : ℕ) (A V D : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b)
    (hA : A = V * D * V⁻¹) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (a : ℕ) (ha : a < m) :
    taylorBlock x ⟨(a + 1) * (k + 1), jump_label_lt (a + 1) m k p ha⟩ =
      V *ᵥ (fun n => taylorPoly k (↑h * D n n) * (V⁻¹ *ᵥ taylorBlock x ⟨a * (k + 1),
        jump_label_lt a m k p (le_of_lt ha)⟩) n
        + ↑h * (V⁻¹ *ᵥ b) n * taylorSrcPoly k (↑h * D n n)) := by
  classical
  have hMA : (h • A) = V * (h • D) * V⁻¹ := by rw [hA]; exact smul_simil h V D
  have hMpow : ∀ r : ℕ, (h • A) ^ r = V * ((h • D) ^ r) * V⁻¹ :=
    simil_pow (h • A) V (h • D) hMA hV1 hV2
  have hnn : ∀ n : N, (h • D) n n = ↑h * D n n := fun n => by simp
  have hdD : ∀ i j : N, i ≠ j → (h • D) i j = 0 := by
    intro i j hij
    simp [hd i j hij]
  have hdiag : ∀ (r : ℕ) (n : N) (u : QState N),
      ((h • D) ^ r *ᵥ u) n = (↑h * D n n) ^ r * u n := by
    intro r n u
    have hdr : ∀ i j : N, i ≠ j → ((h • D) ^ r) i j = 0 := by
      intro i j hij
      rw [diag_pow (h • D) hdD r i j, if_neg hij]
    rw [diag_mulVec ((h • D) ^ r) hdr u n, diag_pow (h • D) hdD r n n, if_pos rfl, hnn n]
  have htransport : ∀ (r : ℕ) (u : QState N),
      (h • A) ^ r *ᵥ (V *ᵥ u) = V *ᵥ ((h • D) ^ r *ᵥ u) := by
    intro r u
    have h1 : (V * (h • D) ^ r * V⁻¹) * V = V * (h • D) ^ r := by
      rw [Matrix.mul_assoc, hV2, Matrix.mul_one]
    calc (h • A) ^ r *ᵥ (V *ᵥ u) = (V * (h • D) ^ r * V⁻¹) *ᵥ (V *ᵥ u) := by rw [hMpow r]
      _ = ((V * (h • D) ^ r * V⁻¹) * V) *ᵥ u :=
          Matrix.mulVec_mulVec u (V * (h • D) ^ r * V⁻¹) V
      _ = (V * (h • D) ^ r) *ᵥ u := by rw [h1]
      _ = V *ᵥ ((h • D) ^ r *ᵥ u) := (Matrix.mulVec_mulVec u V ((h • D) ^ r)).symm
  set w : QState N := V⁻¹ *ᵥ taylorBlock x ⟨a * (k + 1),
    jump_label_lt a m k p (le_of_lt ha)⟩ with hw
  set βc : QState N := V⁻¹ *ᵥ b with hβc
  have hB : taylorBlock x ⟨a * (k + 1), jump_label_lt a m k p (le_of_lt ha)⟩ = V *ᵥ w := by
    rw [hw, Matrix.mulVec_mulVec, hV1, Matrix.one_mulVec]
  have hb : b = V *ᵥ βc := by rw [hβc, Matrix.mulVec_mulVec, hV1, Matrix.one_mulVec]
  have hdata : ∑ i ∈ Finset.range (k + 1),
      (((Nat.factorial i : ℕ) : ℂ)⁻¹ • ((h • A) ^ i *ᵥ
        taylorBlock x ⟨a * (k + 1), jump_label_lt a m k p (le_of_lt ha)⟩))
      = V *ᵥ (fun n => taylorPoly k (↑h * D n n) * w n) := by
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (((Nat.factorial i : ℕ) : ℂ)⁻¹ • ((h • A) ^ i *ᵥ
          taylorBlock x ⟨a * (k + 1), jump_label_lt a m k p (le_of_lt ha)⟩))
        = V *ᵥ (((Nat.factorial i : ℕ) : ℂ)⁻¹ • ((h • D) ^ i *ᵥ w)) := by
      intro i _
      rw [hB, htransport i, ← Matrix.mulVec_smul]
    rw [Finset.sum_congr rfl (fun i hi => hterm i hi), ← Matrix.mulVec_sum]
    congr 1
    funext n
    rw [Finset.sum_apply]
    have hrew : ∀ i ∈ Finset.range (k + 1),
        (((Nat.factorial i : ℕ) : ℂ)⁻¹ • ((h • D) ^ i *ᵥ w)) n
        = ((↑h * D n n) ^ i / ((Nat.factorial i : ℕ) : ℂ)) * w n := by
      intro i _
      rw [Pi.smul_apply, smul_eq_mul, hdiag i n w, div_eq_mul_inv]
      ring
    rw [Finset.sum_congr rfl (fun i hi => hrew i hi), ← Finset.sum_mul, taylorPoly]
  have hsrc : ∑ i ∈ Finset.range (k + 1),
      (if i = 0 then (0 : QState N)
        else (((Nat.factorial i : ℕ) : ℂ)⁻¹) • (h • ((h • A) ^ (i - 1) *ᵥ b)))
      = V *ᵥ (fun n => ↑h * βc n * taylorSrcPoly k (↑h * D n n)) := by
    have hf : ∀ i ∈ Finset.range k,
        (if (i + 1) = 0 then (0 : QState N)
          else (((Nat.factorial (i + 1) : ℕ) : ℂ)⁻¹) • (h • ((h • A) ^ ((i + 1) - 1) *ᵥ b)))
        = V *ᵥ ((((Nat.factorial (i + 1) : ℕ) : ℂ)⁻¹) • (h • ((h • D) ^ i *ᵥ βc))) := by
      intro i _
      rw [if_neg (show ¬((i + 1 : ℕ) = 0) by omega), show i + 1 - 1 = i from rfl, hb,
        htransport i, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    rw [Finset.sum_range_succ', if_pos rfl, add_zero,
      Finset.sum_congr rfl (fun i hi => hf i hi), ← Matrix.mulVec_sum]
    congr 1
    funext n
    rw [Finset.sum_apply]
    have hrew : ∀ i ∈ Finset.range k,
        ((((Nat.factorial (i + 1) : ℕ) : ℂ)⁻¹) • (h • ((h • D) ^ i *ᵥ βc))) n
        = (↑h * βc n) * ((↑h * D n n) ^ i / ((Nat.factorial (i + 1) : ℕ) : ℂ)) := by
      intro i _
      rw [Pi.smul_apply, smul_eq_mul, Pi.smul_apply, Complex.real_smul, hdiag i n βc,
        div_eq_mul_inv]
      ring
    rw [Finset.sum_congr rfl (fun i hi => hrew i hi), ← Finset.mul_sum, taylorSrcPoly]
  have hjump := taylorV2_block_jump m k p (h • A) h x_in b x hx (a + 1)
    (show 1 ≤ a + 1 by omega) ha
  rw [hjump]
  refine Eq.trans (Finset.sum_congr rfl fun i _ =>
    taylorV2_inBlockClosed m k p (h • A) h x_in b x hx a ha ↑i
      (Nat.lt_succ_iff.mp i.isLt)) ?_
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (((Nat.factorial j : ℕ) : ℂ)⁻¹ • ((h • A) ^ j *ᵥ
        taylorBlock x ⟨a * (k + 1), jump_label_lt a m k p (le_of_lt ha)⟩))
      + (if j = 0 then (0 : QState N)
        else (((Nat.factorial j : ℕ) : ℂ)⁻¹) • (h • ((h • A) ^ (j - 1) *ᵥ b)))) (k + 1),
    Finset.sum_add_distrib, hdata, hsrc, ← Matrix.mulVec_add]
  rfl

theorem taylorV2_block_conj (m k p : ℕ) (A V D : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b)
    (hA : A = V * D * V⁻¹) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) :
    ∀ (j : ℕ) (hjm : j ≤ m),
    taylorBlock x (taylorTimeLabel m k p j hjm) =
      V *ᵥ conjSeq k h D (V⁻¹ *ᵥ x_in) (V⁻¹ *ᵥ b) j := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 := taylorV2_block_zero m k p (h • A) h x_in b x hx
    show taylorBlock x (taylorTimeLabel m k p 0 (Nat.zero_le m)) = _
    rw [h0]
    show x_in = V *ᵥ (V⁻¹ *ᵥ x_in)
    rw [Matrix.mulVec_mulVec, hV1, Matrix.one_mulVec]
  | succ j ih =>
    intro hjm
    have ha : j < m := by omega
    have hstep := taylorV2_block_evolution m k p A V D h x_in b x hx hA hV1 hV2 hd j ha
    have hih : taylorBlock x ⟨j * (k + 1), jump_label_lt j m k p (le_of_lt ha)⟩
        = V *ᵥ conjSeq k h D (V⁻¹ *ᵥ x_in) (V⁻¹ *ᵥ b) j := ih (Nat.le_of_lt ha)
    show taylorBlock x ⟨(j + 1) * (k + 1),
      jump_label_lt (j + 1) m k p ha⟩ = _
    rw [hstep, hih, Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec]
    exact congrArg _ (funext fun n => rfl)

theorem hA_eigen_norm_le (A V D : Matrix N N ℂ)
    (hA : A = V * D * V⁻¹) (_hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1)
    (hd : ∀ i j : N, i ≠ j → D i j = 0) (h : ℝ) (_hh : 0 < h) (hnorm : ‖h • A‖ ≤ 1)
    (n : N) : ‖(h : ℂ) * D n n‖ ≤ 1 := by
  classical
  set e : QState N := Pi.single n (1 : ℂ) with he
  set v : QState N := V *ᵥ e with hv
  have hene : e ≠ 0 := by
    intro h0
    have h2 : e n = (0 : ℂ) := by
      have h3 := congrFun h0 n
      simpa using! h3
    have h4 : e n = (1 : ℂ) := by rw [he]; simp
    exact one_ne_zero (h4.symm.trans h2)
  have hvne : v ≠ 0 := by
    intro h0
    have h1 : V⁻¹ *ᵥ v = 0 := by rw [h0, Matrix.mulVec_zero]
    rw [hv, Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec] at h1
    exact hene h1
  have hvpos : 0 < ‖stateVector v‖ :=
    norm_pos_iff.mpr fun hc => hvne ((stateVector_eq_zero_iff v).mp hc)
  have hDve : D *ᵥ e = (D n n) • e := by
    funext n'
    rw [diag_mulVec D hd e n', Pi.smul_apply, smul_eq_mul]
    by_cases hnn : n' = n
    · subst hnn
      rfl
    · have he0 : e n' = 0 := by rw [he]; simp [hnn]
      rw [he0, mul_zero, mul_zero]
  have hAv : A *ᵥ v = (D n n) • v := by
    rw [hv, hA, Matrix.mulVec_mulVec, Matrix.mul_assoc, hV2, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hDve, ← Matrix.mulVec_smul]
  have hzv : (h • A) *ᵥ v = ((h : ℂ) * D n n) • v := by
    rw [Matrix.smul_mulVec, hAv, ← smul_assoc, Complex.real_smul]
  have hle := stateVector_mulVec_norm_le (h • A) v
  rw [hzv, show stateVector (((h : ℂ) * D n n) • v)
      = ((h : ℂ) * D n n) • stateVector v from rfl, norm_smul] at hle
  have h2 : ‖h • A‖ * ‖stateVector v‖ ≤ 1 * ‖stateVector v‖ :=
    mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  exact le_of_mul_le_mul_right (hle.trans h2) hvpos

omit [Fintype N] [DecidableEq N] in

theorem per_coordinate_error (m k : ℕ) (hk : 5 ≤ k) (hm : 0 < m)
    (hF : 2 * m ≤ Nat.factorial (k + 1)) (h : ℝ) (hh : 0 < h)
    (D : Matrix N N ℂ) (y βc : QState N) (n : N)
    (hre : (D n n).re ≤ 0) (hz1 : ‖(h : ℂ) * D n n‖ ≤ 1) (j : ℕ) (hjm : j ≤ m) :
    ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ ≤
      2.8 * (j : ℝ) * (‖y n‖ + (m : ℝ) * (h * ‖βc n‖)) /
        ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
  have hF0 : (0 : ℝ) < ((Nat.factorial (k + 1) : ℕ) : ℝ) := by positivity
  have hFm : (2 * m : ℝ) ≤ ((Nat.factorial (k + 1) : ℕ) : ℝ) := by exact_mod_cast hF
  have hzre : ((h : ℂ) * D n n).re ≤ 0 := by
    have h1 : ((h : ℂ) * D n n).re = h * (D n n).re := by simp
    rw [h1]
    exact mul_nonpos_of_nonneg_of_nonpos hh.le hre
  have hzpow1 : ‖(h : ℂ) * D n n‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (by positivity) hz1
  have hzpowk : ‖(h : ℂ) * D n n‖ ^ k ≤ 1 := pow_le_one₀ (by positivity) hz1
  have hdiv1 : (7 / 6 : ℝ) * ‖(h : ℂ) * D n n‖ ^ (k + 1) /
      ((Nat.factorial (k + 1) : ℕ) : ℝ) ≤ (7 / 6 : ℝ) * 1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hF0 hF0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzpow1 (by norm_num))
      (le_of_lt hF0)
  have hd1 : ‖Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n)‖ ≤
      (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
    have h1 := taylorPoly_defect k ((h : ℂ) * D n n) hk hz1
    calc ‖Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n)‖
        ≤ (7 / 6 : ℝ) * ‖(h : ℂ) * D n n‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := h1
      _ ≤ (7 / 6 : ℝ) * 1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) := hdiv1
      _ = (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by rw [mul_one]
  have hexp1 : ‖Complex.exp ((h : ℂ) * D n n)‖ ≤ 1 :=
    complex_norm_exp_le_one ((h : ℂ) * D n n) hzre
  have hΦb : ∀ j : ℕ, ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)‖ ≤
      ‖y n‖ + (j : ℝ) * (h * ‖βc n‖) := by
    intro j
    have h1 := duhamelCoord_norm_le (D n n) (y n) (βc n) hre ((j : ℝ) * h)
      (mul_nonneg (Nat.cast_nonneg j) hh.le)
    linarith
  have hE0 : (fun (j : ℕ) => ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
      - conjSeq k h D y βc j n‖) 0 = 0 := by
    simp [zero_mul, duhamelCoord_zero, conjSeq]
  have hΦnn : ∀ j : ℕ, 0 ≤ ‖y n‖ + (j : ℝ) * (h * ‖βc n‖) := fun _ => by positivity
  have hstep : ∀ (j : ℕ), (j : ℝ) ≤ (m : ℝ) →
      (fun (j : ℕ) => ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
        - conjSeq k h D y βc j n‖) (j + 1)
        ≤ (1 + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ))
            * (fun (j : ℕ) => ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
              - conjSeq k h D y βc j n‖) j
          + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
            * (fun (j : ℕ) => ‖y n‖ + (j : ℝ) * (h * ‖βc n‖)) j
          + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) * (h * ‖βc n‖) := by
    intro j hjm'
    show ‖duhamelCoord (D n n) (y n) (βc n) (((j + 1 : ℕ) : ℝ) * h)
        - conjSeq k h D y βc (j + 1) n‖ ≤ _
    have hτ : ((j + 1 : ℕ) : ℝ) * h = (j : ℝ) * h + h := by push_cast; ring
    by_cases hlam : D n n = 0
    · have hz0 : (h : ℂ) * D n n = 0 := by simp [hlam]
      have hT1 : taylorPoly k ((h : ℂ) * D n n) = 1 := by rw [hz0]; exact taylorPoly_zero k
      have hS1 : taylorSrcPoly k ((h : ℂ) * D n n) = 1 := by
        rw [hz0]; exact taylorSrcPoly_zero (by omega)
      have h2 := duhamelCoord_step_lam_zero (lam := D n n) (yv := y n) (βv := βc n)
        hlam h ((j : ℝ) * h)
      have h3 : conjSeq k h D y βc (j + 1) n
          = taylorPoly k ((h : ℂ) * D n n) * conjSeq k h D y βc j n
            + h * βc n * taylorSrcPoly k ((h : ℂ) * D n n) := rfl
      rw [hτ, h2, h3, hT1, hS1]
      have hEq2 : duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) + ↑h * βc n
          - (1 * conjSeq k h D y βc j n + ↑h * βc n * 1)
          = duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n := by ring
      rw [hEq2]
      have hE1 : (1 + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ))
          * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖
          = ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖
            + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
              * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
                - conjSeq k h D y βc j n‖ := by ring
      have hE2 : 0 ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
          * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ :=
        mul_nonneg (by positivity) (norm_nonneg _)
      have hE3 : 0 ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
          * (‖y n‖ + (j : ℝ) * (h * ‖βc n‖)) := mul_nonneg (by positivity) (by positivity)
      have hE4 : 0 ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) * (h * ‖βc n‖) :=
        mul_nonneg (by positivity) (by positivity)
      linarith
    · have hzne : (h : ℂ) * D n n ≠ 0 := by
        intro hc
        apply hlam
        rcases mul_eq_zero.mp hc with hc1 | hc2
        · exact absurd hc1 (by exact_mod_cast hh.ne')
        · exact hc2
      have hd2z := exp_src_defect k ((h : ℂ) * D n n) hk hz1 hzne
      have hdiv2 : (7 / 6 : ℝ) * ‖(h : ℂ) * D n n‖ ^ k /
          ((Nat.factorial (k + 1) : ℕ) : ℝ)
          ≤ (7 / 6 : ℝ) * 1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
        rw [div_le_div_iff₀ hF0 hF0]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzpowk (by norm_num))
          (le_of_lt hF0)
      have hd2' : ‖(Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)
          - taylorSrcPoly k ((h : ℂ) * D n n)‖ ≤
          (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
        calc ‖(Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)
            - taylorSrcPoly k ((h : ℂ) * D n n)‖
            ≤ (7 / 6 : ℝ) * ‖(h : ℂ) * D n n‖ ^ k
              / ((Nat.factorial (k + 1) : ℕ) : ℝ) := hd2z
          _ ≤ (7 / 6 : ℝ) * 1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) := hdiv2
          _ = (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by rw [mul_one]
      have h2 := duhamelCoord_step (lam := D n n) (yv := y n) (βv := βc n)
        (h := h) (τ := (j : ℝ) * h) hlam
      have h3 : conjSeq k h D y βc (j + 1) n
          = taylorPoly k ((h : ℂ) * D n n) * conjSeq k h D y βc j n
            + h * βc n * taylorSrcPoly k ((h : ℂ) * D n n) := rfl
      have hexpz : Complex.exp (D n n * (h : ℂ)) = Complex.exp ((h : ℂ) * D n n) := by
        rw [mul_comm]
      have hc0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have hsrcconv : βc n * (Complex.exp ((h : ℂ) * D n n) - 1) / D n n
          = h * βc n * ((Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv,
          show (h : ℂ) * βc n * ((Complex.exp ((h : ℂ) * D n n) - 1)
              * ((h : ℂ)⁻¹ * (D n n)⁻¹))
              = βc n * (Complex.exp ((h : ℂ) * D n n) - 1) * (D n n)⁻¹
                * ((h : ℂ) * (h : ℂ)⁻¹) from by ring,
          mul_inv_cancel₀ hc0, mul_one]
      rw [hτ]
      have hEeq : Complex.exp ((h : ℂ) * D n n)
            * (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n)
            + (Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n))
              * conjSeq k h D y βc j n
            + h * βc n * ((Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)
              - taylorSrcPoly k ((h : ℂ) * D n n))
          = duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h + h) - conjSeq k h D y βc (j + 1) n := by
        rw [h2, hexpz, hsrcconv, h3]
        ring
      have hwb : ‖conjSeq k h D y βc j n‖
          ≤ ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)‖
            + ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ := by
        have h1 : conjSeq k h D y βc j n
            = duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
              - (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
                - conjSeq k h D y βc j n) := by ring
        conv_lhs => rw [h1]
        exact norm_sub_le (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h))
          (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n)
      have t1 : ‖Complex.exp ((h : ℂ) * D n n)
            * (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n)‖
          ≤ ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ := by
        calc ‖Complex.exp ((h : ℂ) * D n n)
              * (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n)‖
            = ‖Complex.exp ((h : ℂ) * D n n)‖
              * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ :=
              norm_mul (Complex.exp ((h : ℂ) * D n n))
                (duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n)
          _ ≤ 1 * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ :=
              mul_le_mul_of_nonneg_right hexp1 (norm_nonneg _)
          _ = ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ :=
              by rw [one_mul]
      have t2 : ‖(Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n))
            * conjSeq k h D y βc j n‖
          ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
            * (‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)‖
              + ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖) := by
        calc ‖(Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n))
              * conjSeq k h D y βc j n‖
            = ‖Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n)‖
              * ‖conjSeq k h D y βc j n‖ :=
              norm_mul (Complex.exp ((h : ℂ) * D n n) - taylorPoly k ((h : ℂ) * D n n))
                (conjSeq k h D y βc j n)
          _ ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) * ‖conjSeq k h D y βc j n‖ :=
              mul_le_mul_of_nonneg_right hd1 (norm_nonneg _)
          _ ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
              * (‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)‖
                + ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖) :=
              mul_le_mul_of_nonneg_left hwb (by positivity)
      have hnormh : ‖(h : ℂ) * βc n‖ = h * ‖βc n‖ := by
        have h1 : ‖(h : ℂ)‖ = h := by
          calc ‖(h : ℂ)‖ = |h| := Complex.norm_real h
            _ = h := abs_of_nonneg hh.le
        rw [Complex.norm_mul, h1]
      have t3 : ‖h * βc n * ((Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)
            - taylorSrcPoly k ((h : ℂ) * D n n))‖
          ≤ (h * ‖βc n‖) * ((7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) := by
        calc ‖h * βc n * ((Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)
              - taylorSrcPoly k ((h : ℂ) * D n n))‖
            = (h * ‖βc n‖) * ‖(Complex.exp ((h : ℂ) * D n n) - 1) / ((h : ℂ) * D n n)
                - taylorSrcPoly k ((h : ℂ) * D n n)‖ := by
              rw [norm_mul, hnormh]
          _ ≤ (h * ‖βc n‖) * ((7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hd2' (by positivity)
      have hΦj := hΦb j
      have hg1 : (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
          * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)‖
          ≤ (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
            * (‖y n‖ + (j : ℝ) * (h * ‖βc n‖)) :=
        mul_le_mul_of_nonneg_left hΦj (by positivity)
      have hfin3 : ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖
          + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
            * (‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)‖
              + ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖)
          + (h * ‖βc n‖) * ((7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ))
          ≤ (1 + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ))
              * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖
            + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
              * (‖y n‖ + (j : ℝ) * (h * ‖βc n‖))
            + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) * (h * ‖βc n‖) := by
        have hid : (1 + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ))
            * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖
            = ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖
              + (7 / 6 : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ)
                * ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h) - conjSeq k h D y βc j n‖ := by
          ring
        linarith [hg1, hid]
      rw [← hEeq]
      refine le_trans ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) hfin3
  exact scalar_gronwall m hm _ hF0 hFm ‖y n‖ (h * ‖βc n‖) (by positivity) (by positivity)
    (fun (j : ℕ) => ‖duhamelCoord (D n n) (y n) (βc n) ((j : ℝ) * h)
      - conjSeq k h D y βc j n‖)
    (fun (j : ℕ) => ‖y n‖ + (j : ℝ) * (h * ‖βc n‖)) hE0
    (fun _ => norm_nonneg _) hΦnn (fun _ => le_rfl) hstep j
    (by exact_mod_cast hjm)

end Evolution

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
