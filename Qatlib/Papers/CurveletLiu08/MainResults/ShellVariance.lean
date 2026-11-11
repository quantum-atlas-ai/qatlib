/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CurveletLiu08.MainResults.RadialVariance

/-!
# Shell variance estimates

This module controls the shell cutoff parameter and normalizes assumed perpendicular and
parallel variance estimates. The theorem `source_theorem4` uses a positive cutoff probability to
pass from restricted integrals to conditional means.

These constructions accompany the results of [Liu2009].

## Main statements

* `etaC_pos`: proves positivity of the shell cutoff under positive scale parameters.
* `etaC_le_eps`: bounds the shell cutoff using the radius comparison.
* `source_theorem4`: derives conditional shell variance bounds from integral bounds.

## References

* [Liu, 2009][Liu2009]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.CurveletLiu08.MainResults

/-- The shell cutoff `(δ / βtilde) * (n - 2) / exp 1` is positive when `δ = ε * β`, the scale
parameters are positive, and `n ≥ 4`. See [Liu2009]. -/
theorem etaC_pos (n : ℕ) (hn : 4 ≤ n) (β βtilde δ ε ηc : ℝ)
    (hε : 0 < ε) (hβ : 0 < β) (hβt : 0 < βtilde) (hδ : δ = ε * β)
    (hηc : ηc = (δ / βtilde) * ((n : ℝ) - 2) / Real.exp 1) :
    0 < ηc := by
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 2 < n)
    linarith
  rw [hηc, hδ]
  have hδpos : 0 < ε * β := mul_pos hε hβ
  positivity

/-- If `β ≤ βtilde` and `δ = ε * β`, the shell cutoff is at most `ε * ((n - 2) / exp 1)` under
the given nonnegativity assumptions. See [Liu2009]. -/
theorem etaC_le_eps (n : ℕ) (hn : 4 ≤ n) (β βtilde δ ε ηc : ℝ)
    (hε : 0 ≤ ε) (hβt : 0 < βtilde) (hδ : δ = ε * β) (hβle : β ≤ βtilde)
    (hηc : ηc = (δ / βtilde) * ((n : ℝ) - 2) / Real.exp 1) :
    ηc ≤ ε * (((n : ℝ) - 2) / Real.exp 1) := by
  have hratio : β / βtilde ≤ 1 := (div_le_one hβt).mpr hβle
  have hcoef : 0 ≤ ((n : ℝ) - 2) / Real.exp 1 := by
    have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      linarith
    exact div_nonneg hn2 (Real.exp_pos 1).le
  rw [hηc, hδ]
  calc ε * β / βtilde * ((n : ℝ) - 2) / Real.exp 1
      = ε * (β / βtilde) * (((n : ℝ) - 2) / Real.exp 1) := by ring
    _ ≤ ε * 1 * (((n : ℝ) - 2) / Real.exp 1) := by gcongr
    _ = ε * (((n : ℝ) - 2) / Real.exp 1) := by ring

/-- The assumed shell integral estimates yield the displayed conditional perpendicular and
parallel variance bounds when the cutoff probability is positive. This is the normalization
step for Theorem 4 of [Liu2009]. -/
theorem source_theorem4
    (n : ℕ) (_hn : 4 ≤ n) (β βtilde δ ε ηc S : ℝ)
    (_hβ : 0 < β) (_hβt : 0 < βtilde) (_hδ : δ = ε * β) (hS : 1 ≤ S)
    (hβle : β ≤ βtilde)
    (hηc : ηc = (δ / βtilde) * ((n : ℝ) - 2) / Real.exp 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → ℝ) (b θ : Ω → EuclideanSpace ℝ (Fin n))
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hPr : 0 < PrScaleLe P a ηc)
    (horth : ∫ ω in {ω | a ω ≤ ηc}, orthVar (b ω) (θ ω) ∂P ≤
        ((n : ℝ) - 1) * ε * β ^ 2 * (507 + C₁ / (n : ℝ)) * S * PrScaleLe P a ηc)
    (hpar : ∫ ω in {ω | a ω ≤ ηc}, parVar (b ω) (θ ω) ∂P ≤
        β ^ 2 * (23 + C₂ / ((n : ℝ) ^ 2)) * PrScaleLe P a ηc) :
    condExpect P a (fun ω => orthVar (b ω) (θ ω)) ηc ≤
        ((n : ℝ) - 1) * ε * β ^ 2 * (507 + C₁ / (n : ℝ)) * S ∧
    condExpect P a (fun ω => parVar (b ω) (θ ω)) ηc ≤
        β ^ 2 * (23 + C₂ / ((n : ℝ) ^ 2)) := by
  refine ⟨?_, ?_⟩
  · exact condExpect_le_of_setIntegral_le P a _ ηc _ hPr horth
  · exact condExpect_le_of_setIntegral_le P a _ ηc _ hPr hpar

end Qatlib.Papers.CurveletLiu08.MainResults
