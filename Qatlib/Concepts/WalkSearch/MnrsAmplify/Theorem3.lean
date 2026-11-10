/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma2Sear
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MnrsAmplify
open scoped Real BigOperators

private theorem mnrs_log_seventy_two : Real.log 72 ≤ 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 72)).mpr
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 6
  norm_num [Finset.sum_range_succ] at hs
  linarith only [hs]

theorem mnrs_order_form_cost (ε c₁ c₂ U C δ : ℝ) (tMax : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmax : (3 : ℝ)^tMax*Real.arcsin (Real.sqrt ε) ≤ 3*π/4)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hcU : c₁ ≤ 2*U/Real.sqrt δ) (hcc : c₂ ≤ C) :
    2*(3 : ℝ)^tMax*(c₁*(Real.log 72+3)+c₂) ≤
      99*(1/Real.sqrt ε)*((1/Real.sqrt δ)*U+C) := by
  have hrε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hrδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hroot1 : Real.sqrt ε ≤ 1 := by simpa using Real.sqrt_le_sqrt hε1
  have ha0 : 0 ≤ Real.arcsin (Real.sqrt ε) :=
    (Real.arcsin_pos.mpr hrε).le
  have hsin : Real.sin (Real.arcsin (Real.sqrt ε)) = Real.sqrt ε :=
    Real.sin_arcsin (by linarith [hrε]) hroot1
  have hroot_angle : Real.sqrt ε ≤ Real.arcsin (Real.sqrt ε) := by
    simpa only [hsin] using Real.sin_le ha0
  have hscale : 2*(3 : ℝ)^tMax ≤ 5/Real.sqrt ε := by
    apply (le_div_iff₀ hrε).mpr
    have he := mul_le_mul_of_nonneg_left hroot_angle (by positivity : (0 : ℝ) ≤ 3^tMax)
    nlinarith only [he, hmax, Real.pi_lt_d2]
  have hU : 0 ≤ U := by
    have hh := (le_div_iff₀ hrδ).mp hcU
    nlinarith only [hh, mul_nonneg hc₁ hrδ.le]
  have hUδ : 0 ≤ U/Real.sqrt δ := div_nonneg hU hrδ.le
  have hlog0 : 0 ≤ Real.log 72 := Real.log_nonneg (by norm_num)
  have hmass : c₁*(Real.log 72+3)+c₂ ≤ 16*(U/Real.sqrt δ)+C := by
    have hl8 : Real.log 72+3 ≤ 8 := by linarith only [mnrs_log_seventy_two]
    calc
      _ ≤ c₁*8+c₂ := add_le_add (mul_le_mul_of_nonneg_left hl8 hc₁) le_rfl
      _ ≤ (2*U/Real.sqrt δ)*8+C := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (5/Real.sqrt ε)*(16*(U/Real.sqrt δ)+C) :=
      mul_le_mul hscale hmass (by positivity) (by positivity)
    _ ≤ 99*(1/Real.sqrt ε)*((1/Real.sqrt δ)*U+C) := by
      have hn := mul_nonneg (inv_nonneg.mpr hrε.le) (add_nonneg hUδ hC)
      have hu := mul_nonneg (inv_nonneg.mpr hrε.le) hUδ
      have hc := mul_nonneg (inv_nonneg.mpr hrε.le) hC
      simp only [div_eq_mul_inv] at hu hc hUδ ⊢
      nlinarith only [hu, hc]

theorem mnrs_search_theorem_three_abstract : Theorem3 := by
  intro W _ _ _ Mr unmarkRefl hMneg hMid x₀ hx₀ ε hε hε1 hmass tMax R c₁ c₂ hc₁ hc₂
    costR costMark Rs hxRs hclose hRRs hfix hbound hcost hmark hwin hmin
  have hγ0 : (0 : ℝ) < 1 / 72 := by norm_num
  have hγ1 : (1 : ℝ) / 72 ≤ 1 / 40 := by norm_num
  have h2 := mnrs_tolerant_raa_lemma_two W Mr unmarkRefl hMneg hMid x₀ hx₀
    (1 / 72) hγ0 hγ1 ε hε hε1 hmass tMax R c₁ c₂ hc₁ hc₂ costR costMark Rs
    hxRs hclose hRRs hfix hbound hcost hmark hwin hmin
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hp
    exact mnrs_zero_mass_tolerant_success Mr unmarkRefl hMid x₀ hx₀ hp R
      (Nat.max tMax 1) hfix
  · intro hp
    have h2' := h2.1 hp
    norm_num at h2' ⊢
    exact h2'
  · have h72 : (1 : ℝ) / (1 / 72) = 72 := by norm_num
    have hcost := h2.2
    rw [h72] at hcost
    exact hcost
  · intro U C δ hδ hδ1 hC hcU hcc
    have h72 : (1 : ℝ) / (1 / 72) = 72 := by norm_num
    have hcost := h2.2
    rw [h72] at hcost
    exact hcost.trans (mnrs_order_form_cost ε c₁ c₂ U C δ tMax hε hε1 hc₁ hc₂
      hwin.2 hδ hC hcU hcc)

end Qatlib.Concepts.WalkSearch.MnrsAmplify
