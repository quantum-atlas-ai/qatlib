/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3CorrectedTigh
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchTimeout
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Unknown-count search budgets for perceptron mistakes

Specializes verified unknown-count marked-item search to confidence budgets used for perceptron
mistake finding. The results bound worst-case prefix iterations, geometric retry failure, and
the empty-marked-set branch for the search step in [WiebeKapoorSvore2016].

## Main statements

* `failure_and_iterations`: There is an initial stage count with the stated square-root
  iteration budget such that reach mass for any nonempty marked set is at most `δ` at the chosen
  cutoff and all later stages.
* `parameter_budget`: At confidence `ε * γ^2`, empty marked sets yield failure mass one, while
  nonempty marked sets have the stated square-root logarithmic iteration budget and reach-mass
  bound at all later stages [WiebeKapoorSvore2016].

## References

* [Wiebe et al., 2016][WiebeKapoorSvore2016]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPerceptron16.MistakeSearch

open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

/-- For a nonempty finite search domain, there is an initial stage count at most `6 * sqrt N`
after which `k` further stages have prefix-iteration cost at most `(6 + k) * sqrt N` and
nonempty marked-set reach mass at most `(3 / 4)^k`. -/
theorem bbht_budget {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) :
    ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧
      ∀ k : ℕ, (WorstPrefixIterations (ExponentialSizes (Fintype.card I)) (K + k) : ℝ)
          ≤ (6 + (k : ℝ)) * Real.sqrt (Fintype.card I) ∧
        ∀ A : Finset I, 0 < A.card →
          RetryReach A (ExponentialSizes (Fintype.card I)) (K + k) ≤ (3 / 4 : ℝ) ^ k := by
  have h := theorem3Corrected (I := I) hN
  dsimp only at h
  exact h.2.2.2

/-- The retry count given by the natural ceiling of `log δ / log (3 / 4)`. -/
def retryCount (δ : ℝ) : ℕ := Nat.ceil (Real.log δ / Real.log (3 / 4))

/-- For `0 < δ ≤ 1`, the chosen retry count makes `(3 / 4)^retryCount δ` at most `δ`. -/
theorem retryCount_failure (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (3 / 4 : ℝ) ^ retryCount δ ≤ δ := by
  have hlog34neg : Real.log (3 / 4 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
  have htnn : 0 ≤ Real.log δ / Real.log (3 / 4) :=
    div_nonneg_of_nonpos hlogδ hlog34neg.le
  have hk : Real.log δ / Real.log (3 / 4) ≤ (retryCount δ : ℝ) := Nat.le_ceil _
  have hbase : (0 : ℝ) < (3 / 4 : ℝ) ^ retryCount δ := by positivity
  have hlogeq : Real.log ((3 / 4 : ℝ) ^ retryCount δ)
      = (retryCount δ : ℝ) * Real.log (3 / 4) := Real.log_pow _ _
  have ht : (Real.log δ / Real.log (3 / 4)) * Real.log (3 / 4) = Real.log δ := by
    field_simp [hlog34neg.ne']
  have hstep : Real.log ((3 / 4 : ℝ) ^ retryCount δ) ≤ Real.log δ := by
    rw [hlogeq, ← ht]
    exact mul_le_mul_of_nonpos_right hk hlog34neg.le
  exact (Real.log_le_log_iff hbase hδ0).mp hstep

/-- There is an initial stage count with the stated square-root iteration budget such that reach
mass for any nonempty marked set is at most `δ` at the chosen cutoff and all later stages. -/
theorem failure_and_iterations
    {I : Type*} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧
      (WorstPrefixIterations (ExponentialSizes (Fintype.card I)) (K + retryCount δ) : ℝ)
        ≤ (6 + (retryCount δ : ℝ)) * Real.sqrt (Fintype.card I) ∧
      ∀ A : Finset I, 0 < A.card → ∀ j : ℕ,
        RetryReach A (ExponentialSizes (Fintype.card I)) (K + retryCount δ + j) ≤ δ := by
  obtain ⟨K, hK, hmain⟩ := bbht_budget (I := I) hN
  refine ⟨K, hK, (hmain (retryCount δ)).1, ?_⟩
  intro A hA j
  have h1 := (hmain (retryCount δ + j)).2 A hA
  rw [← Nat.add_assoc] at h1
  have h2 : (3 / 4 : ℝ) ^ (retryCount δ + j) ≤ (3 / 4 : ℝ) ^ retryCount δ := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ j)
  exact h1.trans (h2.trans (retryCount_failure δ hδ0 hδ1))

/-- The retry count is at most `log (1 / δ) / log (4 / 3) + 1` for `0 < δ ≤ 1`. -/
theorem retryCount_le (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (retryCount δ : ℝ) ≤ Real.log (1 / δ) / Real.log (4 / 3) + 1 := by
  have hlog34neg : Real.log (3 / 4 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hlog43 : Real.log (4 / 3 : ℝ) = -Real.log (3 / 4) := by
    rw [show (4 / 3 : ℝ) = (3 / 4)⁻¹ by norm_num, Real.log_inv]
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
  have hlog1 : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  have hquot : Real.log δ / Real.log (3 / 4) = Real.log (1 / δ) / Real.log (4 / 3) := by
    rw [hlog43, hlog1]
    field_simp
  have htnn : 0 ≤ Real.log δ / Real.log (3 / 4) :=
    div_nonneg_of_nonpos hlogδ hlog34neg.le
  have hlt := Nat.ceil_lt_add_one htnn
  rw [hquot] at hlt
  rw [retryCount, hquot]
  exact (le_of_lt hlt)

/-- The retry-based iteration budget is bounded by the explicit constant times `sqrt N * (1 +
log (1 / δ))`. -/
theorem iteration_budget_asymptotic
    {N : ℕ} (_hN : 0 < N) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (M : ℝ)
    (hM : M ≤ (6 + (retryCount δ : ℝ)) * Real.sqrt (N : ℝ)) :
    M ≤ (7 + (Real.log (4 / 3))⁻¹) * Real.sqrt (N : ℝ) * (1 + Real.log (1 / δ)) := by
  have hNnonneg : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hlog43pos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    nlinarith [hδ1]
  have hk := retryCount_le δ hδ0 hδ1
  have hlog43le1 : Real.log (4 / 3 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith
  have hk' : (retryCount δ : ℝ)
      ≤ (Real.log (4 / 3))⁻¹ * (1 + Real.log (1 / δ)) := by
    have h1 : Real.log (1 / δ) / Real.log (4 / 3)
        = (Real.log (4 / 3))⁻¹ * Real.log (1 / δ) := by
      field_simp
    rw [h1] at hk
    have h2 : (0 : ℝ) ≤ (Real.log (4 / 3))⁻¹ * Real.log (1 / δ) :=
      mul_nonneg (inv_nonneg.mpr hlog43pos.le) hlogδ
    have hinv : (1 : ℝ) ≤ (Real.log (4 / 3))⁻¹ :=
      (one_le_inv₀ hlog43pos).mpr hlog43le1
    nlinarith [hk, h2, hinv]
  have h6 : (6 : ℝ) ≤ 6 * (1 + Real.log (1 / δ)) := by nlinarith
  have hsum : (6 + (retryCount δ : ℝ))
      ≤ (7 + (Real.log (4 / 3))⁻¹) * (1 + Real.log (1 / δ)) := by
    have hsplit : (7 + (Real.log (4 / 3))⁻¹) * (1 + Real.log (1 / δ))
        = 7 * (1 + Real.log (1 / δ)) + (Real.log (4 / 3))⁻¹ * (1 + Real.log (1 / δ)) := by
      ring
    rw [hsplit]
    nlinarith
  calc M ≤ (6 + (retryCount δ : ℝ)) * Real.sqrt (N : ℝ) := hM
    _ ≤ ((7 + (Real.log (4 / 3))⁻¹) * (1 + Real.log (1 / δ))) * Real.sqrt (N : ℝ) := by
        apply mul_le_mul_of_nonneg_right hsum hNnonneg
    _ = (7 + (Real.log (4 / 3))⁻¹) * Real.sqrt (N : ℝ) * (1 + Real.log (1 / δ)) := by ring

/-- There is an initial stage count at most `6 * sqrt N` whose chosen retry prefix has the
stated square-root logarithmic iteration bound. -/
theorem parameter_budget_iteration_bound
    {I : Type*} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧
      (WorstPrefixIterations (ExponentialSizes (Fintype.card I)) (K + retryCount δ) : ℝ)
        ≤ (7 + (Real.log (4 / 3))⁻¹) * Real.sqrt (Fintype.card I)
            * (1 + Real.log (1 / δ)) := by
  obtain ⟨K, hK, hcost, -⟩ := failure_and_iterations (I := I) hN δ hδ0 hδ1
  exact ⟨K, hK, iteration_budget_asymptotic hN δ hδ0 hδ1 _ hcost⟩

/-- For an empty marked set, every finite-budget search has failure mass one and mass zero at
every returned index. -/
theorem empty_marked_branch
    {I : Type*} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I) :
    (∀ stage budget : ℕ,
        FiniteBudgetMass (∅ : Finset I) (ExponentialSizes (Fintype.card I)) stage budget none
          = 1) ∧
      ∀ stage budget : ℕ, ∀ i : I,
        FiniteBudgetMass (∅ : Finset I) (ExponentialSizes (Fintype.card I)) stage budget
          (some i) = 0 := by
  have h := theorem3Corrected (I := I) hN
  dsimp only at h
  obtain ⟨-, hfin, hempty, -⟩ := h
  refine ⟨hempty, ?_⟩
  intro stage budget i
  have hnf := (hfin (∅ : Finset I) stage budget).2.2 i
  simpa using hnf (by simp)

/-- At confidence `ε * γ^2`, empty marked sets yield failure mass one, while nonempty marked
sets have the stated square-root logarithmic iteration budget and reach-mass bound at all
later stages [WiebeKapoorSvore2016]. -/
theorem parameter_budget
    {I : Type*} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I)
    (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (hδ : ε * γ ^ 2 ≤ 1) :
    (∀ stage budget : ℕ,
        FiniteBudgetMass (∅ : Finset I) (ExponentialSizes (Fintype.card I)) stage budget none
          = 1) ∧
      ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧
        (WorstPrefixIterations (ExponentialSizes (Fintype.card I)) (K + retryCount (ε * γ ^ 2))
            : ℝ)
          ≤ (7 + (Real.log (4 / 3))⁻¹) * Real.sqrt (Fintype.card I)
              * (1 + Real.log (1 / (ε * γ ^ 2))) ∧
        ∀ A : Finset I, 0 < A.card → ∀ j : ℕ,
          RetryReach A (ExponentialSizes (Fintype.card I))
            (K + retryCount (ε * γ ^ 2) + j) ≤ ε * γ ^ 2 := by
  have hδ0 : 0 < ε * γ ^ 2 := by positivity
  obtain ⟨hempty, -⟩ := empty_marked_branch (I := I) hN
  obtain ⟨K, hK, hcost, hfail⟩ :=
    failure_and_iterations (I := I) hN (ε * γ ^ 2) hδ0 hδ
  exact ⟨hempty, K, hK,
    iteration_budget_asymptotic hN (ε * γ ^ 2) hδ0 hδ _ hcost, hfail⟩

end Qatlib.Papers.QPerceptron16.MistakeSearch
