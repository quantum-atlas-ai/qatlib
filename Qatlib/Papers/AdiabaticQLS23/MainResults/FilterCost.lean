/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Filtering errors and retry costs

Formalizes scalar filtering and repetition estimates associated with [CostaEtAl2025]. The
geometric distribution `retryPMF` gives exact expected attempts and failures, while
`paperRepetitionSeries` specifies the weighted series used in the paper cost expressions.

The module evaluates both cost models, proves conditional comparisons between them, and relates
filter accuracy to the target error. The example
`lower_failure_bound_is_not_expectation_upper_bound` shows that substituting a lower failure
bound into the repetition series need not bound the actual expected attempts.

## Main statements

* `expectedAttempts_eq`: Evaluates the expected number of attempts as `1 / (1 - r)`.
* `paperTotalCost_eq`: Expands the paper cost using the squared repetition denominator.
* `actual_cost_le_paper_cost`: Bounds the exact cost under an explicit domination condition.
* `actual_error_le_target`: Transfers a filtered fidelity bound to the target scalar error
  estimate.

## References

* [Costa et al., 2025][CostaEtAl2025]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults

noncomputable section

open scoped BigOperators

/-- The scalar failure-ratio expression `δ * (1 - εf ^ 2)`. -/
def filterFailureRatio (δ εf : ℝ) : ℝ := δ * (1 - εf ^ 2)

/-- The geometric mass `(1 - r) * r ^ n` for `n` failures before success. -/
def retryMass (r : ℝ) (n : ℕ) : ℝ := (1 - r) * r ^ n

/-- The geometric retry mass is nonnegative for `r ∈ [0, 1]`. -/
theorem retryMass_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (n : ℕ) :
    0 ≤ retryMass r n := by
  unfold retryMass
  exact mul_nonneg (sub_nonneg.mpr h1) (pow_nonneg h0 n)

/-- For `r ∈ [0, 1)`, the geometric retry masses sum to one. -/
theorem hasSum_retryMass {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℕ => retryMass r n) 1 := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - r)
  have hne : (1 - r) ≠ 0 := by linarith
  simpa [retryMass, hne] using h

/-- The probability mass function of the number of failures before success, with mass `(1 - r) *
r ^ n`. -/
noncomputable abbrev retryPMF (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (retryMass r n), by
    have hnn : HasSum (fun n : ℕ => Real.toNNReal (retryMass r n)) (1 : NNReal) := by
      simpa using (hasSum_retryMass h0 h1).toNNReal (fun n => retryMass_nonneg h0 h1.le n)
    simpa [ENNReal.ofReal] using ENNReal.hasSum_coe.mpr hnn⟩

/-- The real value of `retryPMF` at `n` equals `retryMass r n`. -/
theorem retryPMF_apply {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    (retryPMF r h0 h1 n).toReal = retryMass r n := by
  have h : retryPMF r h0 h1 n = ENNReal.ofReal (retryMass r n) := rfl
  rw [h, ENNReal.toReal_ofReal (retryMass_nonneg h0 h1.le n)]

/-- For `|r| < 1`, the weighted geometric series `∑ (n + 1) * r ^ n` sums to `1 / (1 - r) ^ 2`. -/
theorem hasSum_weighted_repetitions {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * r ^ n) (1 / (1 - r) ^ 2) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (𝕜 := ℝ) (by simpa using hr)
  simpa [Nat.choose_one_right] using h

/-- The geometric expectation of the number of attempts, counting the final successful attempt. -/
def expectedAttempts (r : ℝ) : ℝ := ∑' n : ℕ, (n + 1 : ℝ) * retryMass r n

/-- The geometric expectation of the number of failures before success. -/
def expectedFailures (r : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * retryMass r n

/-- For `r ∈ [0, 1)`, the expected number of attempts is `1 / (1 - r)`. See [CostaEtAl2025]. -/
theorem expectedAttempts_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    expectedAttempts r = 1 / (1 - r) := by
  unfold expectedAttempts
  have h := (hasSum_weighted_repetitions (r := r)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1)).mul_left (1 - r)
  have h' : HasSum (fun n : ℕ => (n + 1 : ℝ) * retryMass r n)
      ((1 - r) * (1 / (1 - r) ^ 2)) := by
    convert! h using 1
    ext n
    simp [retryMass, mul_comm, mul_left_comm, mul_assoc]
  rw [h'.tsum_eq]
  have hne : (1 - r) ≠ 0 := by linarith
  field_simp

/-- For `r ∈ [0, 1)`, the expected number of failures is `r / (1 - r)`. See [CostaEtAl2025]. -/
theorem expectedFailures_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    expectedFailures r = r / (1 - r) := by
  unfold expectedFailures
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := r) (by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1)).mul_left (1 - r)
  have h' : HasSum (fun n : ℕ => (n : ℝ) * retryMass r n)
      ((1 - r) * (r / (1 - r) ^ 2)) := by
    convert! h using 1
    ext n
    simp [retryMass, mul_comm, mul_left_comm, mul_assoc]
  rw [h'.tsum_eq]
  have hne : (1 - r) ≠ 0 := by linarith
  field_simp

/-- For `r ∈ [0, 1)`, the expected number of failures is one less than the expected number of
attempts. -/
theorem expectedFailures_eq_expectedAttempts_sub_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    expectedFailures r = expectedAttempts r - 1 := by
  rw [expectedFailures_eq h0 h1, expectedAttempts_eq h0 h1]
  have hne : (1 - r) ≠ 0 := by linarith
  field_simp
  ring

/-- The repetition-series expression `1 / (1 - r) ^ 2` used in the paper cost model. -/
def paperRepetitionSeries (r : ℝ) : ℝ := 1 / (1 - r) ^ 2

/-- For `|r| < 1`, the series with terms `(n + 1) * r ^ n` sums to `paperRepetitionSeries r`.
See [CostaEtAl2025]. -/
theorem hasSum_paperRepetitionSeries {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * r ^ n) (paperRepetitionSeries r) := by
  simpa [paperRepetitionSeries] using hasSum_weighted_repetitions hr

/-- For `r ∈ [0, 1)`, the expected number of attempts is at most `paperRepetitionSeries r`. See
[CostaEtAl2025]. -/
theorem paperRepetitionSeries_ge_expectedAttempts {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    expectedAttempts r ≤ paperRepetitionSeries r := by
  rw [expectedAttempts_eq h0 h1, paperRepetitionSeries]
  have hp : 0 < 1 - r := by linarith
  have hge : 1 ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ hp]
    linarith
  calc
    1 / (1 - r) = 1 * (1 / (1 - r)) := by ring
    _ ≤ (1 / (1 - r)) * (1 / (1 - r)) := by gcongr
    _ = 1 / (1 - r) ^ 2 := by
      field_simp [ne_of_gt hp]

/-- The paper filtering-cost expression `κ * log (2 / εf) * (paperRepetitionSeries r + 1) / 2`. -/
def paperFilterCost (κ εf r : ℝ) : ℝ :=
  (1 / 2) * κ * Real.log (2 / εf) * (paperRepetitionSeries r + 1)

/-- Splits the paper filtering cost into the initial filtering term and a term proportional to
`paperRepetitionSeries r - 1`. See [CostaEtAl2025]. -/
theorem paperFilterCost_eq (κ εf r : ℝ) :
    paperFilterCost κ εf r
      = κ * Real.log (2 / εf)
        + (1 / 2) * κ * Real.log (2 / εf) * (paperRepetitionSeries r - 1) := by
  unfold paperFilterCost
  ring

/-- The adiabatic cost per attempt `α * κ / Δ` multiplied by `paperRepetitionSeries r`. -/
def paperAdiabaticRepeatCost (α κ Δ r : ℝ) : ℝ :=
  (α * κ / Δ) * paperRepetitionSeries r

/-- For nonzero `Δ` and `|r| < 1`, the paper adiabatic repetition cost equals `α * κ / (Δ * (1 -
r) ^ 2)`. See [CostaEtAl2025]. -/
theorem paperAdiabaticRepeatCost_eq {α κ Δ r : ℝ} (hΔ : Δ ≠ 0) (h : |r| < 1) :
    paperAdiabaticRepeatCost α κ Δ r
      = α * κ / (Δ * (1 - r) ^ 2) := by
  have hr1 : r ≠ 1 := (abs_lt.mp h).2.ne
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  unfold paperAdiabaticRepeatCost paperRepetitionSeries
  field_simp [hΔ, h1r]

/-- The sum of the paper filtering cost and paper adiabatic repetition cost. -/
def paperTotalCost (α κ Δ εf r : ℝ) : ℝ :=
  paperFilterCost κ εf r + paperAdiabaticRepeatCost α κ Δ r

/-- For nonzero `Δ` and `|r| < 1`, expands the paper total cost into its filtering and adiabatic
terms with denominator `(1 - r) ^ 2`. See [CostaEtAl2025]. -/
theorem paperTotalCost_eq {α κ Δ εf r : ℝ} (hΔ : Δ ≠ 0) (h : |r| < 1) :
    paperTotalCost α κ Δ εf r
      = (1 / 2) * κ * Real.log (2 / εf) * (1 / (1 - r) ^ 2 + 1)
        + α * κ / (Δ * (1 - r) ^ 2) := by
  unfold paperTotalCost paperFilterCost paperRepetitionSeries
  rw [paperAdiabaticRepeatCost_eq hΔ h]

/-- For nonzero `Δ` and `|r| < 1`, factors `κ` out of the paper total-cost expression. See
[CostaEtAl2025]. -/
theorem paperTotalCost_factor_kappa {α κ Δ εf r : ℝ} (hΔ : Δ ≠ 0) (h : |r| < 1) :
    paperTotalCost α κ Δ εf r
      = κ * ((1 / 2) * Real.log (2 / εf) * (1 / (1 - r) ^ 2 + 1)
              + α / (Δ * (1 - r) ^ 2)) := by
  have hr1 : r ≠ 1 := (abs_lt.mp h).2.ne
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  rw [paperTotalCost_eq hΔ h]
  field_simp [hΔ, h1r]

/-- The alternative adiabatic repetition cost `(β * κ / δ) * paperRepetitionSeries r`. -/
def paperAdiabaticRepeatCostInvDelta (β κ δ r : ℝ) : ℝ :=
  (β * κ / δ) * paperRepetitionSeries r

/-- For nonzero `δ` and `|r| < 1`, the alternative adiabatic cost equals `β * κ / (δ * (1 - r) ^
2)`. See [CostaEtAl2025]. -/
theorem paperAdiabaticRepeatCostInvDelta_eq {β κ δ r : ℝ} (hδ : δ ≠ 0) (h : |r| < 1) :
    paperAdiabaticRepeatCostInvDelta β κ δ r
      = β * κ / (δ * (1 - r) ^ 2) := by
  have hr1 : r ≠ 1 := (abs_lt.mp h).2.ne
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  unfold paperAdiabaticRepeatCostInvDelta paperRepetitionSeries
  field_simp [hδ, h1r]

/-- The sum of the paper filtering cost and the alternative adiabatic cost parameterized by `δ`. -/
def paperTotalCostInvDelta (β κ εf δ r : ℝ) : ℝ :=
  paperFilterCost κ εf r + paperAdiabaticRepeatCostInvDelta β κ δ r

/-- For nonzero `δ` and `|r| < 1`, expands the alternative total cost into the filtering term
and `β * κ / (δ * (1 - r) ^ 2)`. See [CostaEtAl2025]. -/
theorem paperTotalCostInvDelta_eq {β κ εf δ r : ℝ} (hδ : δ ≠ 0) (h : |r| < 1) :
    paperTotalCostInvDelta β κ εf δ r
      = (1 / 2) * κ * Real.log (2 / εf) * (1 / (1 - r) ^ 2 + 1)
        + β * κ / (δ * (1 - r) ^ 2) := by
  unfold paperTotalCostInvDelta paperFilterCost paperRepetitionSeries
  rw [paperAdiabaticRepeatCostInvDelta_eq hδ h]

/-- The initial filtering cost plus half that cost times the exact expected number of failures. -/
def exactFilterCost (κ εf r : ℝ) : ℝ :=
  κ * Real.log (2 / εf)
    + (1 / 2) * κ * Real.log (2 / εf) * expectedFailures r

/-- For `r ∈ [0, 1)`, the exact filtering cost is `κ * log (2 / εf) * (1 + expectedAttempts r) /
2`. -/
theorem exactFilterCost_eq {κ εf r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    exactFilterCost κ εf r
      = (1 / 2) * κ * Real.log (2 / εf) * (1 + expectedAttempts r) := by
  unfold exactFilterCost
  rw [expectedFailures_eq_expectedAttempts_sub_one h0 h1]
  ring

/-- The adiabatic cost per attempt `α * κ / Δ` multiplied by the exact expected number of
attempts. -/
def exactAdiabaticRepeatCost (α κ Δ r : ℝ) : ℝ :=
  (α * κ / Δ) * expectedAttempts r

/-- For nonzero `Δ` and `r ∈ [0, 1)`, the exact adiabatic repetition cost equals `α * κ / (Δ *
(1 - r))`. -/
theorem exactAdiabaticRepeatCost_eq {α κ Δ r : ℝ} (hΔ : Δ ≠ 0)
    (h0 : 0 ≤ r) (h1 : r < 1) :
    exactAdiabaticRepeatCost α κ Δ r = α * κ / (Δ * (1 - r)) := by
  unfold exactAdiabaticRepeatCost
  rw [expectedAttempts_eq h0 h1]
  field_simp [hΔ]

/-- The sum of the exact filtering cost and exact adiabatic repetition cost. -/
def exactTotalCost (α κ Δ εf r : ℝ) : ℝ :=
  exactFilterCost κ εf r + exactAdiabaticRepeatCost α κ Δ r

/-- For nonzero `Δ` and `r ∈ [0, 1)`, expands the exact total cost using the geometric factor `1
/ (1 - r)`. -/
theorem exactTotalCost_eq {α κ Δ εf r : ℝ} (hΔ : Δ ≠ 0)
    (h0 : 0 ≤ r) (h1 : r < 1) :
    exactTotalCost α κ Δ εf r
      = (1 / 2) * κ * Real.log (2 / εf) * (1 + 1 / (1 - r))
        + α * κ / (Δ * (1 - r)) := by
  unfold exactTotalCost
  rw [exactFilterCost_eq h0 h1, exactAdiabaticRepeatCost_eq hΔ h0 h1,
    expectedAttempts_eq h0 h1]

/-- For nonnegative `α` and `κ`, positive `Δ`, `0 < εf ≤ 2`, and `r ∈ [0, 1)`, the exact total
cost is at most the paper total cost at the same `r`. See [CostaEtAl2025]. -/
theorem exactTotalCost_le_paperTotalCost {α κ Δ εf r : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hΔ : 0 < Δ)
    (hεf0 : 0 < εf) (hεf2 : εf ≤ 2) (h0 : 0 ≤ r) (h1 : r < 1) :
    exactTotalCost α κ Δ εf r ≤ paperTotalCost α κ Δ εf r := by
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hlog : 0 ≤ Real.log (2 / εf) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hεf0]
    linarith
  have hE : expectedAttempts r ≤ paperRepetitionSeries r :=
    paperRepetitionSeries_ge_expectedAttempts h0 h1
  have hcoef1 : 0 ≤ (1 / 2) * κ * Real.log (2 / εf) := by positivity
  have hcoef2 : 0 ≤ α * κ / Δ := by positivity
  have h1' : (1 / 2) * κ * Real.log (2 / εf) * (1 + expectedAttempts r)
      ≤ (1 / 2) * κ * Real.log (2 / εf) * (1 + paperRepetitionSeries r) :=
    mul_le_mul_of_nonneg_left (by linarith) hcoef1
  have h1'' : (1 / 2) * κ * Real.log (2 / εf) * (1 + 1 / (1 - r))
      ≤ (1 / 2) * κ * Real.log (2 / εf) * (1 / (1 - r) ^ 2 + 1) := by
    simpa [expectedAttempts_eq h0 h1, paperRepetitionSeries, add_comm] using h1'
  have h2' : (α * κ / Δ) * (1 / (1 - r)) ≤ (α * κ / Δ) * (1 / (1 - r) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hcoef2
    simpa [expectedAttempts_eq h0 h1, paperRepetitionSeries] using hE
  have h2'' : α * κ / (Δ * (1 - r)) ≤ α * κ / (Δ * (1 - r) ^ 2) := by
    calc
      α * κ / (Δ * (1 - r)) = (α * κ / Δ) * (1 / (1 - r)) := by
        field_simp [hΔne]
      _ ≤ (α * κ / Δ) * (1 / (1 - r) ^ 2) := h2'
      _ = α * κ / (Δ * (1 - r) ^ 2) := by
        field_simp [hΔne]
  rw [exactTotalCost_eq hΔne h0 h1, paperTotalCost_eq hΔne (by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1)]
  linarith

/-- The filtered fidelity expression `(1 - δ) / (1 - δ + δ * εf ^ 2)`. -/
def filteredFidelityBound (δ εf : ℝ) : ℝ :=
  (1 - δ) / (1 - δ + δ * εf ^ 2)

/-- The filter tolerance `ε * sqrt ((1 - δ) * (1 - ε ^ 2 / 4)) / ((1 - ε ^ 2 / 2) * sqrt δ)`
associated with target error `ε`. -/
def epsilonFOfEpsilon (δ ε : ℝ) : ℝ :=
  ε * Real.sqrt ((1 - δ) * (1 - ε ^ 2 / 4)) /
    ((1 - ε ^ 2 / 2) * Real.sqrt δ)

/-- When its denominator is nonzero, the complement of the filtered fidelity bound equals `δ *
εf ^ 2 / (1 - δ + δ * εf ^ 2)`. See [CostaEtAl2025]. -/
theorem filteredFidelityBound_complement (δ εf : ℝ)
    (hden : 1 - δ + δ * εf ^ 2 ≠ 0) :
    1 - filteredFidelityBound δ εf
      = δ * εf ^ 2 / (1 - δ + δ * εf ^ 2) := by
  unfold filteredFidelityBound
  field_simp [hden]
  ring

/-- For `0 < δ < 1` and `0 ≤ ε < 1`, substituting `epsilonFOfEpsilon δ ε` makes the filtered
fidelity expression equal `(1 - ε ^ 2 / 2) ^ 2`. See [CostaEtAl2025]. -/
theorem filteredFidelityBound_epsilonF {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (1 - δ) / (1 - δ + δ * (epsilonFOfEpsilon δ ε) ^ 2)
      = (1 - ε ^ 2 / 2) ^ 2 := by
  have hδpos : 0 < 1 - δ := by linarith
  have h1e : 0 < 1 - ε ^ 2 / 2 := by nlinarith [sq_nonneg ε, hε1]
  have h1e4 : 0 < 1 - ε ^ 2 / 4 := by nlinarith [sq_nonneg ε, hε1]
  have hsδ : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt (le_of_lt hδ0)
  have hse : (Real.sqrt ((1 - δ) * (1 - ε ^ 2 / 4))) ^ 2
      = (1 - δ) * (1 - ε ^ 2 / 4) :=
    Real.sq_sqrt (mul_nonneg (le_of_lt hδpos) (le_of_lt h1e4))
  have hεf_sq : (epsilonFOfEpsilon δ ε) ^ 2
      = ε ^ 2 * (1 - δ) * (1 - ε ^ 2 / 4) / (δ * (1 - ε ^ 2 / 2) ^ 2) := by
    unfold epsilonFOfEpsilon
    rw [div_pow, mul_pow, mul_pow, hse, hsδ]
    ring
  rw [hεf_sq]
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have h1ene : (1 - ε ^ 2 / 2) ≠ 0 := ne_of_gt h1e
  have hCD : (1 - ε ^ 2 / 2) ^ 2 + ε ^ 2 * (1 - ε ^ 2 / 4) = 1 := by ring
  calc
    (1 - δ) / (1 - δ + δ * (ε ^ 2 * (1 - δ) * (1 - ε ^ 2 / 4)
        / (δ * (1 - ε ^ 2 / 2) ^ 2)))
        = (1 - δ) / ((1 - δ) * (1 + ε ^ 2 * (1 - ε ^ 2 / 4)
            / (1 - ε ^ 2 / 2) ^ 2)) := by
          field_simp [hδne, h1ene]
    _ = (1 - δ) / ((1 - δ) / (1 - ε ^ 2 / 2) ^ 2) := by
          have hC : (1 - ε ^ 2 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1ene
          have hA : 1 + ε ^ 2 * (1 - ε ^ 2 / 4) / (1 - ε ^ 2 / 2) ^ 2
              = 1 / (1 - ε ^ 2 / 2) ^ 2 := by
            calc
              1 + ε ^ 2 * (1 - ε ^ 2 / 4) / (1 - ε ^ 2 / 2) ^ 2
                  = (1 - ε ^ 2 / 2) ^ 2 / (1 - ε ^ 2 / 2) ^ 2
                      + ε ^ 2 * (1 - ε ^ 2 / 4) / (1 - ε ^ 2 / 2) ^ 2 := by
                    rw [div_self hC]
              _ = ((1 - ε ^ 2 / 2) ^ 2 + ε ^ 2 * (1 - ε ^ 2 / 4))
                    / (1 - ε ^ 2 / 2) ^ 2 := by rw [add_div]
              _ = 1 / (1 - ε ^ 2 / 2) ^ 2 := by rw [hCD]
          rw [hA]
          field_simp [ne_of_gt hδpos, hC]
    _ = (1 - ε ^ 2 / 2) ^ 2 := by
          field_simp [ne_of_gt hδpos, h1ene]

/-- For `0 < δ < 1` and `0 ≤ ε < 1`, the scalar error expression obtained from the chosen filter
tolerance equals `ε`. See [CostaEtAl2025]. -/
theorem two_norm_error_eq {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Real.sqrt (2 - 2 * Real.sqrt
      ((1 - δ) / (1 - δ + δ * (epsilonFOfEpsilon δ ε) ^ 2))) = ε := by
  rw [filteredFidelityBound_epsilonF hδ0 hδ1 hε0 hε1]
  have h1e : 0 ≤ 1 - ε ^ 2 / 2 := by nlinarith [sq_nonneg ε, hε1]
  rw [Real.sqrt_sq h1e]
  have h2 : 2 - 2 * (1 - ε ^ 2 / 2) = ε ^ 2 := by ring
  rw [h2, Real.sqrt_sq hε0]

/-- If `a ≥ 0`, `0 < δ ≤ 1`, `q ≥ 1`, and `a ≤ δ * q`, then `(1 - a / q ^ 2) ^ q` is at least `1
- δ`. See [CostaEtAl2025]. -/
theorem randomized_q_bound {a δ : ℝ} (ha : 0 ≤ a) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (q : ℕ) (hq : 1 ≤ q) (hqδ : a ≤ δ * q) :
    1 - δ ≤ (1 - a / (q : ℝ) ^ 2) ^ q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have hx0 : 0 ≤ a / (q : ℝ) ^ 2 := div_nonneg ha (le_of_lt hq2)
  have hx1 : a / (q : ℝ) ^ 2 ≤ 1 := by
    have hq2ge : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith [hq1, sq_nonneg ((q : ℝ) - 1)]
    have h1 : a / (q : ℝ) ^ 2 ≤ (δ * q) / (q : ℝ) ^ 2 := by gcongr
    have h2 : (δ * q) / (q : ℝ) ^ 2 = δ / q := by field_simp
    have h3 : δ / q ≤ 1 := by rw [div_le_one hqR]; linarith
    calc
      a / (q : ℝ) ^ 2 ≤ (δ * q) / (q : ℝ) ^ 2 := h1
      _ = δ / q := h2
      _ ≤ 1 := h3
  have hbern : 1 + (q : ℝ) * (-(a / (q : ℝ) ^ 2))
      ≤ (1 - a / (q : ℝ) ^ 2) ^ q := by
    have h := one_add_mul_le_pow (a := -(a / (q : ℝ) ^ 2)) (by nlinarith) (n := q)
    simpa using! h
  have hmid : 1 - a / (q : ℝ) ≤ 1 + (q : ℝ) * (-(a / (q : ℝ) ^ 2)) := by
    field_simp
    ring_nf
    nlinarith [hqR, ha, hx0, hx1]
  have hleft : 1 - δ ≤ 1 - a / (q : ℝ) := by
    have : a / (q : ℝ) ≤ δ := by rw [div_le_iff₀ hqR]; linarith
    linarith
  linarith

/-- For `0 ≤ Δ ≤ Real.sqrt 2`, the nested square-root error expression formed from `Δ ^ 2 - Δ ^
4 / 4` equals `Δ`. See [CostaEtAl2025]. -/
theorem delta_sq_relation (Δ : ℝ) (h0 : 0 ≤ Δ) (h1 : Δ ≤ Real.sqrt 2) :
    Real.sqrt (2 - 2 * Real.sqrt (1 - (Δ ^ 2 - Δ ^ 4 / 4))) = Δ := by
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hΔ2 : Δ ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hsqrt2nn,
      mul_nonneg (sub_nonneg.mpr h1) h0]
  have hs : 0 ≤ 1 - Δ ^ 2 / 2 := by nlinarith
  have hid : 1 - (Δ ^ 2 - Δ ^ 4 / 4) = (1 - Δ ^ 2 / 2) ^ 2 := by ring
  rw [hid, Real.sqrt_sq hs]
  have htwo : 2 - 2 * (1 - Δ ^ 2 / 2) = Δ ^ 2 := by ring
  rw [htwo, Real.sqrt_sq h0]

/-- If `δ` and `ell` are nonnegative and `ell ≤ εf ^ 2`, the actual failure expression `δ * (1 -
ell)` lies between `filterFailureRatio δ εf` and `δ`. See [CostaEtAl2025]. -/
theorem source_failure_interval {δ εf ell : ℝ} (hδ : 0 ≤ δ)
    (hell : 0 ≤ ell) (hcap : ell ≤ εf ^ 2) :
    filterFailureRatio δ εf ≤ δ * (1 - ell) ∧ δ * (1 - ell) ≤ δ := by
  unfold filterFailureRatio
  constructor <;> nlinarith

/-- For `0 < δ < 1` and `0 ≤ ε < 1`, a fidelity at least the chosen filtered bound gives `sqrt
(2 - 2 * sqrt fidelity) ≤ ε`. See [CostaEtAl2025]. -/
theorem actual_error_le_target {δ ε fidelity : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hf : filteredFidelityBound δ (epsilonFOfEpsilon δ ε) ≤ fidelity) :
    Real.sqrt (2 - 2 * Real.sqrt fidelity) ≤ ε := by
  calc
    Real.sqrt (2 - 2 * Real.sqrt fidelity) ≤
        Real.sqrt (2 - 2 * Real.sqrt
          (filteredFidelityBound δ (epsilonFOfEpsilon δ ε))) := by
      apply Real.sqrt_le_sqrt
      have := Real.sqrt_le_sqrt hf
      linarith
    _ = ε := two_norm_error_eq hδ0 hδ1 hε0 hε1

/-- If `0 ≤ q ≤ δ < 1`, `r < 1`, and `δ ≤ 2 * r - r ^ 2`, then the expected attempts at failure
rate `q` are bounded by `paperRepetitionSeries r`. See [CostaEtAl2025]. -/
theorem actual_attempts_le_paper_series {q δ r : ℝ}
    (hq0 : 0 ≤ q) (hqd : q ≤ δ) (hδ1 : δ < 1)
    (hr1 : r < 1) (hdom : δ ≤ 2 * r - r ^ 2) :
    expectedAttempts q ≤ paperRepetitionSeries r := by
  rw [expectedAttempts_eq hq0 (lt_of_le_of_lt hqd hδ1), paperRepetitionSeries]
  apply (div_le_div_iff₀ (by linarith : 0 < 1-q)
    (sq_pos_of_pos (by linarith : 0 < 1-r))).mpr
  nlinarith

/-- Under the stated positivity assumptions and `0 ≤ q ≤ δ < 1` with `δ ≤ 2 * r - r ^ 2` and `r
< 1`, the exact cost at failure rate `q` is at most the paper cost at parameter `r`. -/
theorem actual_cost_le_paper_cost {α κ Δ εf q δ r : ℝ}
    (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hΔ : 0 < Δ)
    (hεf0 : 0 < εf) (hεf2 : εf ≤ 2)
    (hq0 : 0 ≤ q) (hqd : q ≤ δ) (hδ1 : δ < 1)
    (hr1 : r < 1) (hdom : δ ≤ 2*r-r^2) :
    exactTotalCost α κ Δ εf q ≤ paperTotalCost α κ Δ εf r := by
  have hE := actual_attempts_le_paper_series hq0 hqd hδ1 hr1 hdom
  have hc : 0 ≤ (1/2:ℝ)*κ*Real.log (2/εf) := by
    have hl : 0 ≤ Real.log (2/εf) := Real.log_nonneg
      ((le_div_iff₀ hεf0).mpr (by linarith))
    positivity
  have ha : 0 ≤ α*κ/Δ := by positivity
  unfold exactTotalCost paperTotalCost
  rw [exactFilterCost_eq hq0 (lt_of_le_of_lt hqd hδ1)]
  unfold exactAdiabaticRepeatCost paperFilterCost paperAdiabaticRepeatCost
  exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) hc)
    (mul_le_mul_of_nonneg_left hE ha)

/-- At `δ = 1 / 2` and `εf = 1`, the failure-ratio expression is zero but its paper repetition
series is strictly below the expected attempts at failure rate `1 / 2`. -/
theorem lower_failure_bound_is_not_expectation_upper_bound :
    filterFailureRatio (1/2) 1 = 0 ∧
      paperRepetitionSeries (filterFailureRatio (1/2) 1) < expectedAttempts (1/2) := by
  rw [expectedAttempts_eq (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)]
  norm_num [filterFailureRatio, paperRepetitionSeries]

end

end Qatlib.Papers.AdiabaticQLS23.MainResults
