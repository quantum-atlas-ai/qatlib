/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NLTSAnshu23.MainResults.Model.SourceModel

@[expose] public section


/-!
# Uniform lower bound for the quantitative NLTS threshold

The arithmetic conclusion of Theorem 5, arXiv:2206.13228v4, p.5.
This proves positivity of the threshold under explicit rate and check-density
hypotheses; it does not assert existence of a code family or circuit lower bounds.
-/

set_option autoImplicit false

noncomputable section
open Qatlib.Papers.NLTSAnshu23.MainResults.Model

namespace Qatlib.Papers.NLTSAnshu23.MainResults

/-- Constant rate and positive check density eventually give a uniform positive
lower bound for the quantitative NLTS energy threshold. -/
theorem epsilonBound_uniformly_positive {δ0 c1 c2 : ℝ}
    (hc1 : 0 < c1) (hδ0 : 0 < δ0) (hc2 : 0 < c2)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 < M) :
    ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (n k mx mz : ℕ), N ≤ n → 0 < n →
        κ * (n : ℝ) ≤ (k : ℝ) →
        M * (n : ℝ) ≤ (mx : ℝ) →
        M * (n : ℝ) ≤ (mz : ℝ) →
        η ≤ epsilonBound n k mx mz δ0 c1 c2 := by
  set L : ℝ := min ((κ / 8) ^ 2) (min δ0 (c2 / 2)) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    have h1 : 0 < (κ / 8) ^ 2 := by positivity
    have h2 : 0 < min δ0 (c2 / 2) := lt_min hδ0 (by linarith)
    exact lt_min h1 h2
  have hfactor : 0 < 1 / (400 * c1) := by positivity
  refine ⟨(1 / (400 * c1)) * M * L, mul_pos (mul_pos hfactor hM) hLpos, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / κ)
  refine ⟨N, ?_⟩
  intro n k mx mz hnN hn hk hmx hmz
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hκn : (2 : ℝ) < κ * (n : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hN hκ
    have hc : κ * (2 / κ) = 2 := by field_simp
    rw [hc] at hmul
    have hle : κ * (N : ℝ) ≤ κ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hNn (le_of_lt hκ)
    linarith
  have hminR : M * (n : ℝ) ≤ ((min mx mz : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min hmx hmz
  have hmdiv : M ≤ ((min mx mz : ℕ) : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    linarith
  have hk1 : κ * (n : ℝ) / 2 ≤ (k : ℝ) - 1 := by linarith
  have hratio_nonneg : 0 ≤ κ / 8 := by positivity
  have hratio : κ / 8 ≤ ((k : ℝ) - 1) / (4 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hprod : (κ / 8) * (4 * (n : ℝ)) = κ * (n : ℝ) / 2 := by ring
    linarith
  have hsq : (κ / 8) ^ 2 ≤ (((k : ℝ) - 1) / (4 * (n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hratio_nonneg hratio 2
  have hmin_le : L ≤
      min ((((k : ℝ) - 1) / (4 * (n : ℝ))) ^ 2) (min δ0 (c2 / 2)) := by
    rw [hLdef]
    exact min_le_min hsq (le_refl _)
  have hquot_nonneg : 0 ≤ ((min mx mz : ℕ) : ℝ) / (n : ℝ) := by positivity
  have hfac_nonneg : 0 ≤ 1 / (400 * c1) := le_of_lt hfactor
  calc (1 / (400 * c1)) * M * L
      ≤ (1 / (400 * c1)) * (((min mx mz : ℕ) : ℝ) / (n : ℝ)) * L := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hLpos)
        exact mul_le_mul_of_nonneg_left hmdiv hfac_nonneg
    _ ≤ (1 / (400 * c1)) * (((min mx mz : ℕ) : ℝ) / (n : ℝ)) *
          min ((((k : ℝ) - 1) / (4 * (n : ℝ))) ^ 2) (min δ0 (c2 / 2)) := by
        apply mul_le_mul_of_nonneg_left hmin_le
        exact mul_nonneg hfac_nonneg hquot_nonneg
    _ = epsilonBound n k mx mz δ0 c1 c2 := by
        rw [epsilonBound, ← Nat.cast_min]


end Qatlib.Papers.NLTSAnshu23.MainResults
