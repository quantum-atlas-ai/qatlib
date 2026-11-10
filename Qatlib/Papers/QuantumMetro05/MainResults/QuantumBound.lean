/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumMetro05.MainResults.Source
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.QuantumBound

open Qatlib.Papers.QuantumMetro05.MainResults.Source

theorem variance_le_Nspread_sq {X : Type} [Fintype X] [DecidableEq X]
    {N : ℕ} (p : FinDist X) (f : Fin N → X → ℝ) {a b : ℝ}
    (ha : ∀ j x, a ≤ f j x) (hb : ∀ j x, f j x ≤ b) :
    p.variance (fun x => ∑ j, f j x) ≤ ((N : ℝ) * spectralSpread a b) ^ 2 := by
  have hrange : ∀ x : X,
      (N : ℝ) * a ≤ ∑ j, f j x ∧ ∑ j, f j x ≤ (N : ℝ) * b :=
    fun x => spectralSumBounds (fun j => f j x) (fun j => ha j x) (fun j => hb j x)
  have h := variance_le_spread_sq p (fun x => ∑ j, f j x)
    (fun x => (hrange x).1) (fun x => (hrange x).2)
  have hs : spectralSpread ((N : ℝ) * a) ((N : ℝ) * b)
      = (N : ℝ) * spectralSpread a b := by
    rw [spectralSpread_def, spectralSpread_def]; ring
  rwa [hs] at h

theorem qc_qq_error_bound {X : Type} [Fintype X] [DecidableEq X]
    {N : ℕ} (hN : 0 < N) (p : FinDist X) (f : Fin N → X → ℝ) {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b) (ha : ∀ j x, a ≤ f j x) (hb : ∀ j x, f j x ≤ b)
    (hcr : δφ * Real.sqrt (p.variance (fun x => ∑ j, f j x))
            ≥ 1 / (2 * Real.sqrt ν)) :
    1 / (Real.sqrt ν * (N : ℝ) * (b - a)) ≤ δφ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hspread : 0 < spectralSpread a b := by rw [spectralSpread_def]; linarith
  have hvarle : p.variance (fun x => ∑ j, f j x)
      ≤ ((N : ℝ) * spectralSpread a b) ^ 2 :=
    variance_le_Nspread_sq p f ha hb
  have hΔhle : Real.sqrt (p.variance (fun x => ∑ j, f j x))
      ≤ (N : ℝ) * spectralSpread a b := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hvarle⟩
  have hΔhpos : 0 < Real.sqrt (p.variance (fun x => ∑ j, f j x)) := by
    by_contra hle
    have hzero : Real.sqrt (p.variance (fun x => ∑ j, f j x)) = 0 :=
      le_antisymm (not_lt.mp hle) (Real.sqrt_nonneg _)
    rw [hzero, mul_zero] at hcr
    have : 0 < 1 / (2 * Real.sqrt ν) := by positivity
    linarith
  have hmain := error_ge_of_variance_bound (δφ := δφ)
    (Δh := Real.sqrt (p.variance (fun x => ∑ j, f j x)))
    (R := (N : ℝ) * spectralSpread a b) hν hΔhpos (by positivity) hΔhle hcr
  have hden2 : 2 * Real.sqrt ν * ((N : ℝ) * spectralSpread a b)
      = Real.sqrt ν * (N : ℝ) * (b - a) := by
    rw [spectralSpread_def]; ring
  have hden : 1 / (2 * Real.sqrt ν * ((N : ℝ) * spectralSpread a b))
      = 1 / (Real.sqrt ν * (N : ℝ) * (b - a)) := by
    rw [hden2]
  rwa [hden] at hmain

theorem eq4_max_variance {N : ℕ} (a b : ℝ) :
    twoPointLaw.variance (twoPointValue ((N : ℝ) * a) ((N : ℝ) * b))
      = ((N : ℝ) * spectralSpread a b) ^ 2 := by
  rw [twoPointLaw_variance, spectralSpread_def, spectralSpread_def]
  ring

theorem eq4_attains_error_bound {N : ℕ} {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b)
    (hcr : δφ * ((N : ℝ) * spectralSpread a b) = 1 / (2 * Real.sqrt ν)) :
    δφ = 1 / (Real.sqrt ν * (N : ℝ) * (b - a)) := by
  have hspread : spectralSpread a b ≠ 0 := by rw [spectralSpread_def]; linarith
  have hden : (N : ℝ) * spectralSpread a b ≠ 0 := by
    by_cases hN : (N : ℝ) = 0
    · rw [hN, zero_mul] at hcr
      have : 0 < 1 / (2 * Real.sqrt ν) := by positivity
      linarith
    · exact mul_ne_zero hN hspread
  have hstep : δφ = (1 / (2 * Real.sqrt ν)) / ((N : ℝ) * spectralSpread a b) := by
    rw [eq_div_iff hden]
    exact hcr
  rw [hstep, div_div]
  have hden2 : 2 * Real.sqrt ν * ((N : ℝ) * spectralSpread a b)
      = Real.sqrt ν * (N : ℝ) * (b - a) := by
    rw [spectralSpread_def]; ring
  rw [hden2]

end Qatlib.Papers.QuantumMetro05.MainResults.QuantumBound
