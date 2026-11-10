/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.GeneralNoise

open scoped BigOperators
open Finset

theorem one_qubit_product_to_sum
    (S : ℕ) (q : Fin S → ℝ) (κ δ : ℝ)
    (hS : 0 < S) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hq : ∀ s, 0 ≤ q s)
    (hD3 : (1 - 2 * δ) ^ 2 ≤ 3 * contractionProduct κ q)
    (_hSbig : Real.log (3 / (1 - 2 * δ) ^ 2) < (S : ℝ)) :
    layerEnvelopeSum q ≥ ((S : ℝ) / (2 * Real.log (1 / κ))) *
      Real.log ((S : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2)) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have h1δ : 0 < 1 - 2 * δ := by linarith
  set a : ℝ := (1 - 2 * δ) ^ 2 with ha
  have ha_pos : 0 < a := by
    rw [ha]; exact sq_pos_of_ne_zero (by linarith)
  have ha_le1 : a ≤ 1 := by
    have h2 : (1 : ℝ) - 2 * δ ≤ 1 := by linarith
    have h3 : 0 ≤ (1 - 2 * δ) * (1 - ((1 : ℝ) - 2 * δ)) :=
      mul_nonneg h1δ.le (sub_nonneg.mpr h2)
    rw [ha]
    nlinarith [h3]
  have hCδ_pos : 0 < Real.log (3 / a) := by
    apply Real.log_pos
    have h31 : (1 : ℝ) < 3 / a := by
      rw [one_lt_div ha_pos]
      nlinarith
    exact h31

  have hfactor : ∀ s, 0 ≤ κ ^ (2 * q s) ∧ κ ^ (2 * q s) ≤ 1 := by
    intro s
    refine ⟨(Real.rpow_pos_of_pos hκ0 _).le,
      Real.rpow_le_one hκ0.le hκ1.le (mul_nonneg zero_le_two (hq s))⟩

  have hprod : contractionProduct κ q ≤ Real.exp (-(∑ s, κ ^ (2 * q s))) :=
    prod_one_sub_le_exp_neg_sum hfactor

  have hsum_le : (∑ s, κ ^ (2 * q s)) ≤ Real.log (3 / a) := by
    have h3 : a / 3 ≤ Real.exp (-(∑ s, κ ^ (2 * q s))) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith [hD3, hprod]
    have h4 : Real.log (a / 3) ≤ -(∑ s, κ ^ (2 * q s)) := by
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < a / 3) h3
      rwa [Real.log_exp] at hlog
    have h5 : Real.log (a / 3) = -Real.log (3 / a) := by
      rw [Real.log_div (ne_of_gt ha_pos) (by norm_num : (3 : ℝ) ≠ 0),
          Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt ha_pos)]
      ring
    linarith

  have hjensen : (S : ℝ) * κ ^ ((∑ s, 2 * q s) / (S : ℝ)) ≤ ∑ s, κ ^ (2 * q s) :=
    jensen_rpow_sum hκ0 hS (fun s => 2 * q s)
  have hsum2 : (∑ s, 2 * q s) = 2 * layerEnvelopeSum q := by
    simp only [layerEnvelopeSum]
    rw [← Finset.mul_sum]
  rw [hsum2] at hjensen

  have hsc : κ ^ ((2 * layerEnvelopeSum q) / (S : ℝ)) * (S : ℝ) ≤ Real.log (3 / a) := by
    linarith [le_trans hjensen hsum_le]
  have hmono : κ ^ ((2 * layerEnvelopeSum q) / (S : ℝ)) ≤ Real.log (3 / a) / (S : ℝ) :=
    (le_div_iff₀ hSpos).mpr hsc

  have hlogκ : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  have hlogpow : Real.log (κ ^ ((2 * layerEnvelopeSum q) / (S : ℝ)))
      = ((2 * layerEnvelopeSum q) / (S : ℝ)) * Real.log κ := Real.log_rpow hκ0 _
  have hlogCD : Real.log (Real.log (3 / a) / (S : ℝ))
      = -Real.log ((S : ℝ) / Real.log (3 / a)) := by
    rw [Real.log_div (ne_of_gt hCδ_pos) (ne_of_gt hSpos),
        Real.log_div (ne_of_gt hSpos) (ne_of_gt hCδ_pos)]
    ring
  have hlogmono : ((2 * layerEnvelopeSum q) / (S : ℝ)) * Real.log κ
      ≤ -Real.log ((S : ℝ) / Real.log (3 / a)) := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hκ0 _) hmono
    rwa [hlogpow, hlogCD] at hlog
  have hsplit : ((2 * layerEnvelopeSum q) / (S : ℝ)) * Real.log κ
      = (layerEnvelopeSum q * (2 * Real.log κ)) / (S : ℝ) := by ring
  rw [hsplit] at hlogmono
  have hmul : layerEnvelopeSum q * (2 * Real.log κ)
      ≤ -Real.log ((S : ℝ) / Real.log (3 / a)) * (S : ℝ) :=
    (div_le_iff₀ hSpos).mp hlogmono
  have hloginvκ : Real.log (1 / κ) = -Real.log κ := by
    rw [one_div]
    exact Real.log_inv κ
  have key : (S : ℝ) * Real.log ((S : ℝ) / Real.log (3 / a))
      ≤ layerEnvelopeSum q * (2 * Real.log (1 / κ)) := by
    rw [hloginvκ]
    linarith
  have hLpos : 0 < Real.log (1 / κ) := by rw [hloginvκ]; linarith
  rw [ge_iff_le, div_mul_eq_mul_div,
    div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Real.log (1 / κ))]
  exact key

theorem one_qubit_lower_bound
    (S : ℕ) (q : Fin S → ℝ) (κ δ : ℝ)
    (hS : 0 < S) (hκ0 : 0 < κ) (_hκ1 : κ ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hq : ∀ s, 0 ≤ q s)
    (hD3 : (1 - 2 * δ) ^ 2 ≤ 3 * contractionProduct κ q) :
    (1 - 2 * δ) ^ 2 ≤ 3 * contractionProduct κ q ∧
    (κ < 1 → Real.log (3 / (1 - 2 * δ) ^ 2) < (S : ℝ) →
      layerEnvelopeSum q ≥ ((S : ℝ) / (2 * Real.log (1 / κ))) *
        Real.log ((S : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2))) ∧
    (κ = 1 → 3 * contractionProduct κ q = 0) := by
  refine ⟨hD3, ?_, ?_⟩
  · intro hlt hs
    exact one_qubit_product_to_sum S q κ δ hS hκ0 hlt hδ0 hδ hq hD3 hs
  · intro hκ
    have hzero : contractionProduct κ q = 0 := by
      have hf : (1 : ℝ) - κ ^ (2 * q ⟨0, hS⟩) = 0 := by
        rw [hκ, Real.one_rpow]
        ring
      rw [contractionProduct]
      exact Finset.prod_eq_zero (Finset.mem_univ _) hf
    rw [hzero]
    ring

structure InfoDimensionData (S K : ℕ) where
  q : Fin S → ℝ
  q_int : ∀ s, ∃ n : ℕ, q s = (n : ℝ)
  overlap : ℝ
  overlap_upper : ∀ s, overlap ≤ (2 : ℝ) ^ (q s - (K : ℝ))
  overlap_lower : 1 / 2 < overlap

theorem information_dimension_lower_bound {S K : ℕ} (_hK : 1 ≤ K)
    (d : InfoDimensionData S K) :
    (∀ s, (K : ℝ) ≤ d.q s) ∧ (K : ℝ) * (S : ℝ) ≤ layerEnvelopeSum d.q := by
  have hqK : ∀ s, (K : ℝ) ≤ d.q s := by
    intro s
    obtain ⟨n, hn⟩ := d.q_int s
    by_contra hlt
    push Not at hlt
    have hnk : n < K := by
      have hnr : (n : ℝ) < (K : ℝ) := by rwa [hn] at hlt
      exact_mod_cast hnr
    have hle : (n : ℝ) - (K : ℝ) ≤ -1 := by
      have hnr : (n : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hnk
      linarith
    have h2 : (2 : ℝ) ^ (d.q s - (K : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).2
      rw [hn]; exact hle
    have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num [Real.rpow_neg_one]
    have : d.overlap ≤ 1 / 2 := by
      calc d.overlap ≤ (2 : ℝ) ^ (d.q s - (K : ℝ)) := d.overlap_upper s
        _ ≤ (2 : ℝ) ^ (-1 : ℝ) := h2
        _ = 1 / 2 := hhalf
    linarith [d.overlap_lower]
  refine ⟨hqK, ?_⟩
  calc (K : ℝ) * (S : ℝ) = ∑ _s : Fin S, (K : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ s : Fin S, d.q s := Finset.sum_le_sum (fun s _ => hqK s)
    _ = layerEnvelopeSum d.q := rfl

theorem layerwise_circuit_size_bound
    (K S : ℕ) (q : Fin S → ℝ) (κ δ : ℝ)
    (_hK : 1 ≤ K) (_hS : 0 < S) (_hκ0 : 0 < κ) (_hκ1 : κ < 1)
    (_hδ0 : 0 ≤ δ) (_hδ : δ < 1 / 2)
    (hKS : (K : ℝ) * (S : ℝ) ≤ layerEnvelopeSum q)
    (hlog : ((S : ℝ) * Real.log ((S : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2))) /
        (2 * Real.log (1 / κ)) ≤ layerEnvelopeSum q) :
    layerEnvelopeSum q ≥ max ((K : ℝ) * (S : ℝ))
      (((S : ℝ) * Real.log ((S : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2))) /
        (2 * Real.log (1 / κ))) := by
  exact max_le hKS hlog

theorem no_uniform_constant_relative_bound
    (κ δ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (Correct : ∀ T : ℕ, (Fin T → ℝ) → Prop)
    (hD3 : ∀ (T : ℕ) (q : Fin T → ℝ), 0 < T → Correct T q → (∀ s, 0 ≤ q s) →
      (1 - 2 * δ) ^ 2 ≤ 3 * contractionProduct κ q)
    (hexist : ∀ T : ℕ, 1 ≤ T → ∃ q : Fin T → ℝ, Correct T q ∧ ∀ s, 0 ≤ q s) :
    ∀ C : ℝ, 0 < C → ∃ (T : ℕ) (q : Fin T → ℝ),
      1 ≤ T ∧ Correct T q ∧ layerEnvelopeSum q > C * (T : ℝ) := by
  intro C hC
  have h1δ : 0 < 1 - 2 * δ := by linarith
  have hLpos : 0 < Real.log (1 / κ) := by
    apply Real.log_pos
    rw [one_div]
    exact one_lt_inv_iff₀.mpr ⟨hκ0, hκ1⟩
  have h2Lpos : (0 : ℝ) < 2 * Real.log (1 / κ) := by linarith
  have hCδpos : 0 < Real.log (3 / (1 - 2 * δ) ^ 2) := by
    apply Real.log_pos
    rw [one_lt_div (sq_pos_of_ne_zero (by linarith))]
    have h2 : (1 : ℝ) - 2 * δ ≤ 1 := by linarith
    have h3 : 0 ≤ (1 - 2 * δ) * (1 - ((1 : ℝ) - 2 * δ)) :=
      mul_nonneg h1δ.le (sub_nonneg.mpr h2)
    nlinarith [h3]

  obtain ⟨T, hT1, hTbigCδ, hTbigExp⟩ :
      ∃ T : ℕ, 1 ≤ T ∧ Real.log (3 / (1 - 2 * δ) ^ 2) < (T : ℝ) ∧
        Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) < (T : ℝ) := by
    refine ⟨(Nat.ceil (max (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
          (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1))).succ,
      Nat.succ_le_succ (Nat.zero_le _), ?_, ?_⟩
    all_goals
      have h3 : (((Nat.ceil (max (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
            (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1))).succ : ℝ)) =
          ((Nat.ceil (max (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
            (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1)) : ℝ)) + 1 :=
        Nat.cast_succ _
      have h2 : max (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
          (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1) ≤
          ((Nat.ceil (max (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
            (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1)) : ℝ)) :=
        Nat.le_ceil _
      linarith [le_max_left (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
        (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1),
        le_max_right (Real.log (3 / (1 - 2 * δ) ^ 2) + 1)
        (Real.log (3 / (1 - 2 * δ) ^ 2) * Real.exp (2 * C * Real.log (1 / κ)) + 1)]
  obtain ⟨q, hqcorr, hqnonneg⟩ := hexist T hT1
  refine ⟨T, q, hT1, hqcorr, ?_⟩
  have hbound := one_qubit_product_to_sum T q κ δ (by omega) hκ0 hκ1 hδ0 hδ hqnonneg
    (hD3 T q (by omega) hqcorr hqnonneg) hTbigCδ
  have hlogstrict :
      2 * C * Real.log (1 / κ) < Real.log ((T : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2)) := by
    have hlogprod : Real.log (Real.log (3 / (1 - 2 * δ) ^ 2) *
        Real.exp (2 * C * Real.log (1 / κ)))
        = Real.log (Real.log (3 / (1 - 2 * δ) ^ 2)) + 2 * C * Real.log (1 / κ) := by
      rw [Real.log_mul (ne_of_gt hCδpos) (Real.exp_ne_zero _), Real.log_exp]
    have hlt : Real.log (Real.log (3 / (1 - 2 * δ) ^ 2) *
        Real.exp (2 * C * Real.log (1 / κ))) < Real.log ((T : ℝ)) :=
      Real.log_lt_log (mul_pos hCδpos (Real.exp_pos _)) hTbigExp
    rw [hlogprod] at hlt
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
    have hdiv : Real.log ((T : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2))
        = Real.log (T : ℝ) - Real.log (Real.log (3 / (1 - 2 * δ) ^ 2)) :=
      Real.log_div (ne_of_gt hTpos) (ne_of_gt hCδpos)
    rw [hdiv]
    linarith
  have hfin : C * (T : ℝ) < ((T : ℝ) / (2 * Real.log (1 / κ))) *
      Real.log ((T : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2)) := by
    have hstep1 : ((T : ℝ) / (2 * Real.log (1 / κ))) * (2 * C * Real.log (1 / κ)) <
        ((T : ℝ) / (2 * Real.log (1 / κ))) *
          Real.log ((T : ℝ) / Real.log (3 / (1 - 2 * δ) ^ 2)) :=
      mul_lt_mul_of_pos_left hlogstrict (by exact div_pos (by positivity) h2Lpos)
    have hstep2 : ((T : ℝ) / (2 * Real.log (1 / κ))) * (2 * C * Real.log (1 / κ))
        = C * (T : ℝ) := by
      field_simp [ne_of_gt h2Lpos]
    linarith
  exact lt_of_lt_of_le hfin hbound

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.GeneralNoise
