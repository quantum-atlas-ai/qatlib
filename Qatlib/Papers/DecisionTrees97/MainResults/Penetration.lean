/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology BigOperators Real

namespace Qatlib.Papers.DecisionTrees97.MainResults

def ScalarClassicalPenetrable (p : ℕ → ℝ → ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∃ t : ℝ, 1 ≤ t ∧ t < (n : ℝ) ^ A ∧ (1 / (n : ℝ)) ^ B < p n t

def ScalarAmplitudePenetrable (a : ℕ → ℝ → ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∃ t : ℝ, 0 ≤ t ∧ t < (n : ℝ) ^ A ∧ (1 / (n : ℝ)) ^ B < a n t

def IsMaxAmplitudeOn (a : ℕ → ℝ → ℝ) (n : ℕ) (T ε : ℝ) : Prop :=
  (∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ a n t = ε) ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T → a n t ≤ ε

def AssumedScalarBound (p a : ℕ → ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ (B D : ℝ), 0 < B → 4 * B < D →
    ∀ (n : ℕ) (t : ℝ) (ε : ℝ), 1 ≤ n → 1 ≤ t → IsMaxAmplitudeOn a n ((n : ℝ) ^ D) ε →
      p n t ≤ (ε / π) * ((D + 1) * Real.log (n : ℝ)) + C * (n : ℝ) ^ (-D / 4)

theorem eventually_decay_le_half (B D C : ℝ) (hD : 4 * B < D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * (n : ℝ) ^ (-D / 4) ≤ (1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B := by
  have he : 0 < D / 4 - B := by linarith
  have htend : Tendsto (fun x : ℝ => x ^ (D / 4 - B)) atTop atTop :=
    tendsto_rpow_atTop he
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htendN : Tendsto (fun n : ℕ => (n : ℝ) ^ (D / 4 - B)) atTop atTop :=
    htend.comp hnat
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 2 * C ≤ (n : ℝ) ^ (D / 4 - B) :=
    htendN.eventually (eventually_ge_atTop (2 * C))
  filter_upwards [hbig, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hstep : C * (n : ℝ) ^ (-D / 4) ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (D / 4 - B)
      * (n : ℝ) ^ (-D / 4) := by
    have h1 : C ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (D / 4 - B) := by linarith
    calc C * (n : ℝ) ^ (-D / 4)
        ≤ ((1 / 2 : ℝ) * (n : ℝ) ^ (D / 4 - B)) * (n : ℝ) ^ (-D / 4) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hnpos _).le
      _ = (1 / 2 : ℝ) * (n : ℝ) ^ (D / 4 - B) * (n : ℝ) ^ (-D / 4) := by ring
  have hprod : (n : ℝ) ^ (D / 4 - B) * (n : ℝ) ^ (-D / 4) = (n : ℝ) ^ (-B) := by
    rw [← Real.rpow_add hnpos]
    try (congr 1; ring)
  have hinv : (n : ℝ) ^ (-B) = (1 / (n : ℝ)) ^ B := by
    rw [one_div, Real.inv_rpow (le_of_lt hnpos) B]
    exact Real.rpow_neg (le_of_lt hnpos) B
  calc C * (n : ℝ) ^ (-D / 4)
      ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (D / 4 - B) * (n : ℝ) ^ (-D / 4) := hstep
    _ = (1 / 2 : ℝ) * ((n : ℝ) ^ (D / 4 - B) * (n : ℝ) ^ (-D / 4)) := by ring
    _ = (1 / 2 : ℝ) * (n : ℝ) ^ (-B) := by rw [hprod]
    _ = (1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B := by rw [hinv]

theorem penetration_amplitude_step
    (B D : ℝ) (hDpos : 0 < D) (n : ℕ) (hn : 2 ≤ n)
    (ε C : ℝ) (hε : 0 ≤ ε)
    (hsmall : C * (n : ℝ) ^ (-D / 4) ≤ (1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B)
    (hbound : (1 / (n : ℝ)) ^ B
      ≤ (ε / π) * ((D + 1) * Real.log (n : ℝ)) + C * (n : ℝ) ^ (-D / 4)) :
    π / (2 * (D + 1)) * (1 / (n : ℝ)) ^ (B + 1) ≤ ε := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hrpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hDp : (0 : ℝ) < D + 1 := by linarith
  have hpipos : (0 : ℝ) < π := Real.pi_pos
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have h1 : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hA : (ε / π) * ((D + 1) * Real.log (n : ℝ)) ≤ (ε / π) * ((D + 1) * (n : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hε hpipos.le)
    nlinarith [hlog, hDp]
  have hstep : (1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B ≤ (ε / π) * ((D + 1) * (n : ℝ)) := by
    linarith [hbound, hsmall, hA]
  have hden : (0 : ℝ) < (D + 1) * (n : ℝ) := mul_pos hDp hnpos
  have hstep' : π * ((1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B) / ((D + 1) * (n : ℝ)) ≤ ε := by
    rw [div_le_iff₀ hden]
    have h2 : π * ((1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B)
        ≤ π * ((ε / π) * ((D + 1) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hstep hpipos.le
    have h3 : π * ((ε / π) * ((D + 1) * (n : ℝ))) = ε * ((D + 1) * (n : ℝ)) := by
      field_simp
      try ring
    linarith [h2, h3]
  have hpow : (1 / (n : ℝ)) ^ (B + 1) = (1 / (n : ℝ)) ^ B * (1 / (n : ℝ)) :=
    Real.rpow_add_one (ne_of_gt hrpos) B
  rw [hpow]
  have hmul : π / (2 * (D + 1)) * ((1 / (n : ℝ)) ^ B * (1 / (n : ℝ)))
      = π * ((1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B) / ((D + 1) * (n : ℝ)) := by
    field_simp
    try ring
  rw [hmul]
  exact hstep'

theorem penetrability_of_assumed_scalar_bound
    (p a : ℕ → ℝ → ℝ) (C : ℝ)
    (hnonneg : ∀ (n : ℕ) (t : ℝ), 0 ≤ a n t)
    (hcont : ∀ (n : ℕ) (T : ℝ), ContinuousOn (a n) (Set.Icc 0 T))
    (hbound : AssumedScalarBound p a C)
    (hclass : ScalarClassicalPenetrable p) :
    ScalarAmplitudePenetrable a := by
  obtain ⟨A, B, hA, hB, hev⟩ := hclass
  set D : ℝ := 4 * B + A + 1 with hDdef
  have hBD : 4 * B < D := by rw [hDdef]; linarith
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hAle : A ≤ D := by rw [hDdef]; linarith
  refine ⟨D + 1, B + 2, by linarith, by linarith, ?_⟩
  have hevsmall : ∀ᶠ n : ℕ in Filter.atTop,
      C * (n : ℝ) ^ (-D / 4) ≤ (1 / 2 : ℝ) * (1 / (n : ℝ)) ^ B :=
    eventually_decay_le_half B D C hBD
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n := eventually_ge_atTop 2
  have hev3 : ∀ᶠ n : ℕ in Filter.atTop, (1 / (n : ℝ)) < π / (2 * (D + 1)) := by
    have htend : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hcpos : (0 : ℝ) < π / (2 * (D + 1)) := by
      apply div_pos Real.pi_pos
      linarith
    exact htend.eventually (Iio_mem_nhds hcpos)
  filter_upwards [hev, hevsmall, hev2, hev3] with n hn hsmall hn2 hlt
  obtain ⟨t, ht1, htA, hpt⟩ := hn
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith

  have htnD : t ≤ (n : ℝ) ^ D := by
    have hle : (n : ℝ) ^ A ≤ (n : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le hn1R hAle
    linarith

  have hTnonneg : (0 : ℝ) ≤ (n : ℝ) ^ D := (Real.rpow_pos_of_pos hnpos _).le
  obtain ⟨tm, htm_mem, htm_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, le_refl 0, hTnonneg⟩ (hcont n ((n : ℝ) ^ D))
  set ε : ℝ := a n tm with hεdef
  have hεnonneg : 0 ≤ ε := by
    rw [hεdef]
    exact hnonneg n tm
  have hmax : IsMaxAmplitudeOn a n ((n : ℝ) ^ D) ε := by
    refine ⟨⟨tm, htm_mem.1, htm_mem.2, rfl⟩, ?_⟩
    intro s hs0 hsT
    exact (isMaxOn_iff.mp htm_max) s ⟨hs0, hsT⟩
  have hb := hbound B D hB hBD n t ε hn1 ht1 hmax
  have hb' : (1 / (n : ℝ)) ^ B
      ≤ (ε / π) * ((D + 1) * Real.log (n : ℝ)) + C * (n : ℝ) ^ (-D / 4) :=
    le_of_lt (lt_of_lt_of_le hpt hb)
  have hcle : π / (2 * (D + 1)) * (1 / (n : ℝ)) ^ (B + 1) ≤ ε :=
    penetration_amplitude_step B D hDpos n hn2 ε C hεnonneg hsmall hb'

  have hrpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hdecay : (1 / (n : ℝ)) ^ (B + 2) < ε := by
    have h1 : (1 / (n : ℝ)) ^ (B + 2) = (1 / (n : ℝ)) ^ (B + 1) * (1 / (n : ℝ)) := by
      rw [show B + 2 = B + 1 + 1 by ring]
      exact Real.rpow_add_one (ne_of_gt hrpos) (B + 1)
    rw [h1]
    calc (1 / (n : ℝ)) ^ (B + 1) * (1 / (n : ℝ))
        < (1 / (n : ℝ)) ^ (B + 1) * (π / (2 * (D + 1))) :=
          mul_lt_mul_of_pos_left hlt (Real.rpow_pos_of_pos hrpos _)
      _ = π / (2 * (D + 1)) * (1 / (n : ℝ)) ^ (B + 1) := by ring
      _ ≤ ε := hcle
  refine ⟨tm, htm_mem.1, ?_, ?_⟩
  · have hltD : (n : ℝ) ^ D < (n : ℝ) ^ (D + 1) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      · exact_mod_cast (by omega : 1 < n)
      · linarith
    exact lt_of_le_of_lt htm_mem.2 hltD
  · exact hdecay

end Qatlib.Papers.DecisionTrees97.MainResults
