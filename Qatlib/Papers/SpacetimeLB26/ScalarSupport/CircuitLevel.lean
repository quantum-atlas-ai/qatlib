/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Filter

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.CircuitLevel

theorem conditional_circuit_achievability
    (K T : ℝ) (ct cq β A Rgad N0 cN : ℝ) (Ngad : Set ℕ)
    (hK : 1 ≤ K) (hT : 1 ≤ T) (hct : 0 < ct) (hcq : 0 < cq)
    (hβ : 0 < β) (hA : 1 ≤ A) (hRgad : 0 < Rgad) (hN0 : 0 ≤ N0) (hcN : 1 ≤ cN)
    (hblock : ∀ x : ℝ, 1 ≤ x → ∃ N ∈ Ngad, x ≤ (N : ℝ) ∧ (N : ℝ) ≤ cN * x)
    (hsim : ∀ (N : ℕ) (ε : ℝ), N ∈ Ngad → 0 < ε → ε ≤ 1 →
      ∃ (err S CFT : ℝ),
        err ≤ T * A * Real.exp (-β * (N : ℝ)) ∧
        0 ≤ S ∧ S ≤ ct * T ∧
        CFT ≤ cq * (N : ℝ) * S) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ (N : ℕ) (diam S CFT : ℝ),
      N ∈ Ngad ∧ diam ≤ ε ∧ S ≤ ct * T ∧
        CFT ≤ cq * ct * cN * (max (max N0 (1 / Rgad)) (1 / β) + 1) * T *
          (K + 1 + Real.log (A * T / ε)) := by
  intro ε hε1 hε2
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hKnn : (0 : ℝ) ≤ K := zero_le_one.trans hK

  have hAT : (1 : ℝ) ≤ A * T := by nlinarith [hA, hT]
  have hATε : 1 ≤ A * T / ε := (one_le_div hε1).mpr (hε2.trans hAT)
  have hL : 0 ≤ Real.log (A * T / ε) := Real.log_nonneg hATε
  set L := Real.log (A * T / ε) with hLdef
  set c0 := max (max N0 (1 / Rgad)) (1 / β) with hc0def
  have h1R : 0 < 1 / Rgad := one_div_pos.mpr hRgad
  have h1β : 0 < 1 / β := one_div_pos.mpr hβ
  have hc0nn : (0 : ℝ) ≤ c0 := le_max_iff.mpr (Or.inl (le_max_iff.mpr (Or.inl hN0)))
  have hW1 : (1 : ℝ) ≤ K + 1 + L := by linarith
  have hWnn : (0 : ℝ) ≤ K + 1 + L := by linarith

  have hN0c0 : N0 ≤ c0 := (le_max_left N0 _).trans (le_max_left _ _)
  have hRc0 : 1 / Rgad ≤ c0 := (le_max_right N0 _).trans (le_max_left _ _)
  have hβc0 : 1 / β ≤ c0 := le_max_right _ _
  have hxN0 : N0 ≤ c0 * (K + 1 + L) := by
    calc N0 = N0 * 1 := (mul_one _).symm
      _ ≤ N0 * (K + 1 + L) := mul_le_mul_of_nonneg_left hW1 hN0
      _ ≤ c0 * (K + 1 + L) := mul_le_mul_of_nonneg_right hN0c0 hWnn
  have hxR : K / Rgad ≤ c0 * (K + 1 + L) := by
    have hstep : K / Rgad = K * (1 / Rgad) := div_eq_mul_one_div K Rgad
    calc K / Rgad = K * (1 / Rgad) := hstep
      _ ≤ K * c0 := mul_le_mul_of_nonneg_left hRc0 hKnn
      _ ≤ (K + 1 + L) * c0 :=
          mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1 + L) hc0nn
      _ = c0 * (K + 1 + L) := mul_comm _ _
  have hxβ : L / β ≤ c0 * (K + 1 + L) := by
    have hstep : L / β = L * (1 / β) := div_eq_mul_one_div L β
    calc L / β = L * (1 / β) := hstep
      _ ≤ (K + 1 + L) * c0 :=
          mul_le_mul (by linarith) hβc0 h1β.le hWnn
      _ = c0 * (K + 1 + L) := mul_comm _ _
  have hxmax : max N0 (max (K / Rgad) (L / β)) ≤ c0 * (K + 1 + L) :=
    max_le hxN0 (max_le hxR hxβ)

  set x := max N0 (max (K / Rgad) (L / β)) with hxdef
  set x' := max 1 x with hx'def
  have hxpos : (0 : ℝ) ≤ x := by
    have h1 : K / Rgad ≤ x := by
      rw [hxdef]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have h2 : (0 : ℝ) < K / Rgad := div_pos (by linarith [hK]) hRgad
    linarith
  have hx' : x' ≤ (c0 + 1) * (K + 1 + L) := by
    rw [hx'def]
    have hmaxle : max (1 : ℝ) x ≤ 1 + x := max_le (by linarith) (by linarith)
    have hfin : 1 + c0 * (K + 1 + L) ≤ (c0 + 1) * (K + 1 + L) := by
      nlinarith [hW1, mul_nonneg hc0nn hWnn]
    have hxx : x ≤ c0 * (K + 1 + L) := by rw [hxdef]; exact hxmax
    nlinarith [hmaxle, hxx, hfin]
  obtain ⟨N, hNmem, hNx', hNcN⟩ := hblock x' (le_max_left 1 x)
  have hNx : x ≤ (N : ℝ) := (le_max_right 1 x).trans hNx'
  obtain ⟨err, S, CFT, herr, hS0, hS, hCFT⟩ := hsim N ε hNmem hε1 hε2
  refine ⟨N, err, S, CFT, hNmem, ?_, hS, ?_⟩
  · have hLβN : L / β ≤ (N : ℝ) := by
      have hLβ : L / β ≤ x := by
        rw [hxdef]
        exact (le_max_right _ _).trans (le_max_right _ _)
      exact hLβ.trans hNx
    have hNb : L ≤ (N : ℝ) * β := (div_le_iff₀ hβ).mp hLβN
    calc err ≤ T * A * Real.exp (-β * (N : ℝ)) := herr
      _ = T * A * Real.exp (-(β * (N : ℝ))) := by rw [neg_mul]
      _ ≤ T * A * Real.exp (-L) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le (by linarith [hNb]))
            (mul_nonneg hTpos.le hApos.le)
      _ = T * A * ((A * T / ε)⁻¹) := by
          rw [Real.exp_neg, Real.exp_log (div_pos (mul_pos hApos hTpos) hε1)]
      _ = ε := by
          field_simp [ne_of_gt hApos, ne_of_gt hTpos, ne_of_gt hε1]
  · have hcNnn : (0 : ℝ) ≤ cN := zero_le_one.trans hcN
    have hx'nn : (0 : ℝ) ≤ cN * x' :=
      mul_nonneg hcNnn (zero_le_one.trans (le_max_left 1 x))
    have hkey : cq * (cN * x') * (ct * T)
        ≤ (cq * ct * cN * (max (max N0 (1 / Rgad)) (1 / β) + 1)) * T * (K + 1 + L) := by
      have hm : cN * x' ≤ cN * ((c0 + 1) * (K + 1 + L)) :=
        mul_le_mul_of_nonneg_left hx' hcNnn
      calc cq * (cN * x') * (ct * T)
          ≤ cq * (cN * ((c0 + 1) * (K + 1 + L))) * (ct * T) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hcq.le)
              (mul_nonneg hct.le hTpos.le)
        _ = (cq * ct * cN * (max (max N0 (1 / Rgad)) (1 / β) + 1)) * T * (K + 1 + L) := by
            rw [hc0def]
            ring
    calc CFT ≤ cq * (N : ℝ) * S := hCFT
      _ ≤ cq * (cN * x') * S :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNcN hcq.le) hS0
      _ ≤ cq * (cN * x') * (ct * T) :=
          mul_le_mul_of_nonneg_left hS (mul_nonneg hcq.le hx'nn)
      _ ≤ (cq * ct * cN * (max (max N0 (1 / Rgad)) (1 / β) + 1)) * T * (K + 1 + L) :=
          hkey

theorem positive_threshold_sufficient
    (dst Nst t : ℕ → ℕ) (pst : ℝ → ℝ) (PL : ℕ → ℝ → ℝ) (C μ : ℝ)
    (hC : 0 < C) (hμ : 0 < μ)
    (hdst_inf : Tendsto dst atTop atTop)
    (hdst1 : ∀ lam, 1 ≤ dst lam)
    (hNst1 : ∀ lam, 1 ≤ Nst lam)
    (_hpst0 : pst 0 = 0)
    (hpst_nonneg : ∀ p, 0 ≤ p → 0 ≤ pst p)
    (hpst_tendsto : Tendsto pst (nhds 0) (nhds 0))
    (hPL_nonneg : ∀ lam p, 0 ≤ p → 0 ≤ PL lam p)
    (hLogNst : Tendsto (fun lam => Real.log ((Nst lam : ℕ) : ℝ) /
        ((dst lam : ℕ) : ℝ)) atTop (nhds 0))
    (ht_dst : ∀ lam, ((dst lam : ℕ) : ℝ) / 2 ≤ ((t lam : ℕ) : ℝ) + 1)
    (hI8 : ∀ (lam : ℕ) (p : ℝ), 0 ≤ p → μ * pst p < 1 →
      PL lam p ≤ C * (Nst lam : ℝ) * (μ * pst p) ^ (t lam + 1) / (1 - μ * pst p)) :
    ∃ p0 : ℝ, 0 < p0 ∧ ∀ p : ℝ, 0 ≤ p → p < p0 →
      Tendsto (fun lam => PL lam p) atTop (nhds 0) := by

  obtain ⟨ε, hε0, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (Metric.tendsto_nhds.mp hpst_tendsto (1 / (2 * μ))
      (div_pos (by norm_num) (mul_pos (by norm_num) hμ)))
  refine ⟨ε, hε0, fun p hp0 hpε => ?_⟩
  have hpstp : |pst p| < 1 / (2 * μ) := by
    have hb : p ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hp0]
      exact hpε
    have hbb := hball p hb
    rwa [Real.dist_eq, sub_zero] at hbb
  rw [abs_of_nonneg (hpst_nonneg p hp0)] at hpstp
  have hζhalf : μ * pst p ≤ 1 / 2 := by
    have h1 : μ * pst p ≤ μ * (1 / (2 * μ)) :=
      mul_le_mul_of_nonneg_left hpstp.le hμ.le
    have h2 : μ * (1 / (2 * μ)) = 1 / 2 := by field_simp [ne_of_gt hμ]
    linarith
  by_cases hζ0 : μ * pst p = 0
  · have hzero : ∀ lam, PL lam p = 0 := by
      intro lam
      have h8 := hI8 lam p hp0 (by rw [hζ0]; norm_num)
      rw [hζ0] at h8
      have hz : (0 : ℝ) ^ (t lam + 1) = 0 := zero_pow (Nat.succ_ne_zero _)
      have hrhs : C * (Nst lam : ℝ) * 0 ^ (t lam + 1) / (1 - 0) = 0 := by
        rw [hz]; ring
      exact le_antisymm (h8.trans_eq hrhs) (hPL_nonneg lam p hp0)
    have hconst : (fun lam => PL lam p) = fun _ : ℕ => (0 : ℝ) := by
      funext lam; rw [hzero lam]
    rw [hconst]
    exact tendsto_const_nhds
  · have hζpos : 0 < μ * pst p :=
      lt_of_le_of_ne (mul_nonneg hμ.le (hpst_nonneg p hp0)) (Ne.symm hζ0)
    have hζ1 : μ * pst p < 1 := by linarith
    have hlogζ : Real.log (μ * pst p) < 0 := by
      have h := Real.log_lt_log hζpos hζ1
      rwa [Real.log_one] at h
    have hdpos : ∀ lam, (0 : ℝ) < ((dst lam : ℕ) : ℝ) := fun lam => by
      exact_mod_cast (hdst1 lam)
    have hden : (0 : ℝ) < 1 - μ * pst p := by linarith

    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hLogNst (-Real.log (μ * pst p) / 4)
      (div_pos (neg_pos.mpr hlogζ) (by norm_num))
    have hbound : ∀ lam : ℕ, N₂ ≤ lam → PL lam p ≤
        C / (1 - μ * pst p) * Real.exp (((dst lam : ℕ) : ℝ) *
          (Real.log (μ * pst p) / 4)) := by
      intro lam hlam
      have h8 := hI8 lam p hp0 (by linarith)
      have hNpos : (0 : ℝ) < ((Nst lam : ℕ) : ℝ) := by exact_mod_cast (hNst1 lam)

      have htd : ((dst lam : ℕ) : ℝ) / 2 ≤ ((t lam + 1 : ℕ) : ℝ) := by
        have h := ht_dst lam
        rw [Nat.cast_succ]
        exact h
      have hstep : ((t lam + 1 : ℕ) : ℝ) * Real.log (μ * pst p)
          ≤ ((dst lam : ℕ) : ℝ) / 2 * Real.log (μ * pst p) :=
        mul_le_mul_of_nonpos_right htd (by linarith)
      have hsplit : ((Nst lam : ℕ) : ℝ) * (μ * pst p) ^ (t lam + 1)
          = Real.exp (Real.log ((Nst lam : ℕ) : ℝ) +
              ((t lam + 1 : ℕ) : ℝ) * Real.log (μ * pst p)) := by
        have e2 : Real.exp (((t lam + 1 : ℕ) : ℝ) * Real.log (μ * pst p))
            = (μ * pst p) ^ (t lam + 1) := by
          rw [← Real.rpow_natCast (μ * pst p) (t lam + 1), Real.rpow_def_of_pos hζpos,
            mul_comm]
        calc ((Nst lam : ℕ) : ℝ) * (μ * pst p) ^ (t lam + 1)
            = Real.exp (Real.log ((Nst lam : ℕ) : ℝ)) * (μ * pst p) ^ (t lam + 1) := by
              rw [Real.exp_log hNpos]
          _ = Real.exp (Real.log ((Nst lam : ℕ) : ℝ)) *
                Real.exp (((t lam + 1 : ℕ) : ℝ) * Real.log (μ * pst p)) := by rw [← e2]
          _ = Real.exp (Real.log ((Nst lam : ℕ) : ℝ) +
                ((t lam + 1 : ℕ) : ℝ) * Real.log (μ * pst p)) :=
              (Real.exp_add _ _).symm
      have hlog := hN₂ lam hlam
      rw [Real.dist_eq, sub_zero, abs_lt] at hlog
      have hdiv : Real.log ((Nst lam : ℕ) : ℝ) / ((dst lam : ℕ) : ℝ)
          < -Real.log (μ * pst p) / 4 := hlog.2
      rw [div_lt_iff₀ (hdpos lam)] at hdiv
      have hkey : (-Real.log (μ * pst p) / 4) * ((dst lam : ℕ) : ℝ) +
          ((dst lam : ℕ) : ℝ) / 2 * Real.log (μ * pst p)
          = ((dst lam : ℕ) : ℝ) * (Real.log (μ * pst p) / 4) := by
        field_simp
        ring
      have hfinal : ((Nst lam : ℕ) : ℝ) * (μ * pst p) ^ (t lam + 1)
          ≤ Real.exp (((dst lam : ℕ) : ℝ) * (Real.log (μ * pst p) / 4)) := by
        rw [hsplit]
        apply Real.exp_le_exp_of_le
        linarith [hdiv, hkey, hstep]
      calc PL lam p
          ≤ C * ((Nst lam : ℕ) : ℝ) * (μ * pst p) ^ (t lam + 1) / (1 - μ * pst p) := h8
        _ = (C / (1 - μ * pst p)) * (((Nst lam : ℕ) : ℝ) * (μ * pst p) ^ (t lam + 1)) := by
            ring
        _ ≤ (C / (1 - μ * pst p)) *
              Real.exp (((dst lam : ℕ) : ℝ) * (Real.log (μ * pst p) / 4)) :=
            mul_le_mul_of_nonneg_left hfinal (div_nonneg hC.le hden.le)

    have hexp0 : Filter.Tendsto
        (fun d : ℝ => Real.exp (d * (Real.log (μ * pst p) / 4)))
        Filter.atTop (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro δ hδ
      rw [Filter.eventually_atTop]
      refine ⟨Real.log (δ / 2) / (Real.log (μ * pst p) / 4) + 1, fun d hd => ?_⟩
      have hc4 : Real.log (μ * pst p) / 4 < 0 := by linarith
      have h1 : d * (Real.log (μ * pst p) / 4)
          ≤ (Real.log (δ / 2) / (Real.log (μ * pst p) / 4) + 1) *
              (Real.log (μ * pst p) / 4) :=
        mul_le_mul_of_nonpos_right hd (by linarith)
      have h2 : (Real.log (δ / 2) / (Real.log (μ * pst p) / 4) + 1) *
              (Real.log (μ * pst p) / 4)
          = Real.log (δ / 2) + Real.log (μ * pst p) / 4 := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_lt hc4), one_mul]
      have hδ2 : (0 : ℝ) < δ / 2 := div_pos hδ (by norm_num)
      have hle : d * (Real.log (μ * pst p) / 4) ≤ Real.log (δ / 2) := by
        rw [h2] at h1
        linarith [h1, hc4]
      calc dist (Real.exp (d * (Real.log (μ * pst p) / 4))) 0
          = Real.exp (d * (Real.log (μ * pst p) / 4)) := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ Real.exp (Real.log (δ / 2)) := Real.exp_le_exp_of_le hle
        _ = δ / 2 := Real.exp_log hδ2
        _ < δ := by linarith
    have hcast : Filter.Tendsto (fun lam => ((dst lam : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      obtain ⟨i, hi⟩ := (Filter.tendsto_atTop_atTop.mp hdst_inf) (Nat.ceil b + 1)
      refine ⟨i, fun lam hlam => ?_⟩
      have h1 : ((Nat.ceil b + 1 : ℕ) : ℝ) ≤ ((dst lam : ℕ) : ℝ) := by
        exact_mod_cast hi lam hlam
      have h2 : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
      have h3 : (Nat.ceil b : ℝ) < ((Nat.ceil b + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self _
      linarith
    have hg : Filter.Tendsto (fun lam => C / (1 - μ * pst p) *
        Real.exp (((dst lam : ℕ) : ℝ) * (Real.log (μ * pst p) / 4)))
        Filter.atTop (nhds 0) := by
      have hc := hexp0.comp hcast
      have hmul := hc.const_mul (C / (1 - μ * pst p))
      simpa [mul_zero] using hmul

    rw [Metric.tendsto_nhds]
    intro δ hδ
    filter_upwards [Metric.tendsto_nhds.mp hg δ hδ,
      Filter.eventually_atTop.mpr ⟨N₂, hbound⟩] with lam hgδ hle
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hPL_nonneg lam p hp0)]
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg (div_nonneg hC.le hden.le) (Real.exp_pos _).le)] at hgδ
    exact lt_of_le_of_lt hle hgδ

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.CircuitLevel
