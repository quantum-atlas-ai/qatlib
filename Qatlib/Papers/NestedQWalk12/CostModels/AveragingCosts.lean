/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Averaging bounds for branch costs

This module develops finite weighted-sum estimates for the averaging argument in
[JefferyKothariMagniez2013]. `overlapLedger` records contributions from retained and replaced
unitary branches, and `withinBudget` selects indices whose costs do not exceed a threshold.

For normalized amplitudes and unit branch states, `averaging_conversion_inner` bounds the real
overlap by 1 minus twice the excluded weight. The remaining results bound excluded weight using
nonnegative costs and a positive multiple of their weighted sum.

## Main statements

* `withinBudget_spec`: membership is equivalent to satisfying the cost threshold.
* `averaging_conversion_inner`: a real overlap bound from excluded branch mass.
* `averaging_query_bound`: a finite weighted tail estimate.
* `averaging_constant_error`: a threshold at k times the weighted cost gives a bound of 1 - 2/k.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NestedQWalk12.CostModels.AveragingCosts

open scoped Real ComplexOrder BigOperators ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The weighted sum with contribution one on branches in C and contribution ⟪s i, U i (s i)⟫
outside C, weighted by squared amplitude norms. -/
def overlapLedger {n : ℕ} (U : Fin n → H ≃ₗᵢ[ℂ] H) (s : Fin n → H)
    (α : Fin n → ℂ) (C : Finset (Fin n)) : ℂ :=
  ∑ i, ((‖α i‖ ^ 2 : ℝ) : ℂ) *
    (if i ∈ C then 1 else ⟪s i, U i (s i)⟫)

/-- The finite set of branch indices whose cost Q i is at most the threshold q. -/
def withinBudget {n : ℕ} (Q : Fin n → ℝ) (q : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Q i ≤ q)

/-- An index belongs to `withinBudget Q q` exactly when its cost is at most q. -/
theorem withinBudget_spec {n : ℕ} (Q : Fin n → ℝ) (q : ℝ) :
    ∀ i, i ∈ withinBudget Q q ↔ Q i ≤ q := by
  intro i
  simp [withinBudget]

/-- For unit branch states and amplitudes whose squared norms sum to one, the real part of
`overlapLedger` is at least 1 minus twice the total squared amplitude outside C. -/
theorem averaging_conversion_inner {n : ℕ} (α : Fin n → ℂ) (s : Fin n → H)
    (U : Fin n → H ≃ₗᵢ[ℂ] H) (C : Finset (Fin n))
    (hs : ∀ i, ‖s i‖ = 1) (hα : ∑ i, ‖α i‖ ^ 2 = 1) :
    (overlapLedger U s α C).re ≥ 1 - 2 * (∑ i ∈ Cᶜ, ‖α i‖ ^ 2) := by

  have hre : (overlapLedger U s α C).re
      = (∑ i ∈ C, ‖α i‖ ^ 2)
        + ∑ i ∈ Cᶜ, ‖α i‖ ^ 2 * (⟪s i, U i (s i)⟫).re := by
    unfold overlapLedger
    rw [Complex.re_sum,
      ← Finset.sum_add_sum_compl C
        (fun i => (((‖α i‖ ^ 2 : ℝ) : ℂ) *
          (if i ∈ C then 1 else ⟪s i, U i (s i)⟫)).re)]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [if_pos hi, mul_one, Complex.ofReal_re]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : i ∉ C := Finset.mem_compl.mp hi
      simp only [if_neg hi', Complex.re_ofReal_mul]

  have hcompl : - (∑ i ∈ Cᶜ, ‖α i‖ ^ 2)
      ≤ ∑ i ∈ Cᶜ, ‖α i‖ ^ 2 * (⟪s i, U i (s i)⟫).re := by
    have hblock : ∀ i ∈ Cᶜ, -(‖α i‖ ^ 2)
        ≤ ‖α i‖ ^ 2 * (⟪s i, U i (s i)⟫).re := by
      intro i _
      have hnorm : ‖⟪s i, U i (s i)⟫‖ ≤ 1 := by
        have h2 : ‖⟪s i, U i (s i)⟫‖ ≤ ‖s i‖ * ‖U i (s i)‖ :=
          norm_inner_le_norm (s i) (U i (s i))
        have h3 : ‖U i (s i)‖ = ‖s i‖ := (U i).norm_map (s i)
        rw [h3, hs i, mul_one] at h2
        exact h2
      have habs : |(⟪s i, U i (s i)⟫).re| ≤
          ‖⟪s i, U i (s i)⟫‖ := Complex.abs_re_le_norm _
      have hge : (⟪s i, U i (s i)⟫).re ≥ -1 := by
        have := neg_le_of_abs_le habs
        linarith
      have hp : (0 : ℝ) ≤ ‖α i‖ ^ 2 := by positivity
      nlinarith [hge, hp]
    calc - (∑ i ∈ Cᶜ, ‖α i‖ ^ 2)
        = ∑ i ∈ Cᶜ, -(‖α i‖ ^ 2) := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ Cᶜ, ‖α i‖ ^ 2 * (⟪s i, U i (s i)⟫).re :=
            Finset.sum_le_sum hblock

  have hCsum : (∑ i ∈ C, ‖α i‖ ^ 2)
      = 1 - ∑ i ∈ Cᶜ, ‖α i‖ ^ 2 := by
    have h := Finset.sum_add_sum_compl C (fun i => ‖α i‖ ^ 2)
    rw [hα] at h
    linarith
  rw [hre]
  linarith [hcompl, hCsum]

/-- For nonnegative weights and costs, the excluded weight times a nonnegative threshold is
bounded by the total weighted cost when C consists exactly of indices at or below that
threshold. -/
theorem averaging_query_bound {n : ℕ} (p Q : Fin n → ℝ) (C : Finset (Fin n))
    (q : ℝ) (hp : ∀ i, 0 ≤ p i) (hQ : ∀ i, 0 ≤ Q i)
    (hC : ∀ i, i ∈ C ↔ Q i ≤ q) (_hq : 0 ≤ q) :
    (∑ i ∈ Cᶜ, p i) * q ≤ ∑ i, p i * Q i := by
  have hstep : (∑ i ∈ Cᶜ, p i) * q ≤ ∑ i ∈ Cᶜ, p i * Q i := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i ∉ C := Finset.mem_compl.mp hi
    have hgt : q < Q i := by
      have := (hC i).not.mp hi'
      exact lt_of_not_ge this
    have := hp i
    nlinarith [hgt, this]
  have hsubset : ∑ i ∈ Cᶜ, p i * Q i ≤ ∑ i, p i * Q i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro i _ _
    exact mul_nonneg (hp i) (hQ i)
  linarith [hstep, hsubset]

/-- For nonnegative weights and costs, retaining indices of cost at most k times the weighted
cost yields 1 minus twice the excluded weight at least 1 - 2/k, provided k and the threshold
are positive. -/
theorem averaging_constant_error {n : ℕ} (p Q : Fin n → ℝ)
    (C : Finset (Fin n)) (k : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hQ : ∀ i, 0 ≤ Q i)
    (hC : ∀ i, i ∈ C ↔ Q i ≤ k * ∑ i, p i * Q i) (hk : 0 < k)
    (hq : 0 < k * ∑ i, p i * Q i) :
    1 - 2 * (∑ i ∈ Cᶜ, p i) ≥ 1 - 2 / k := by
  have hm := averaging_query_bound p Q C (k * ∑ i, p i * Q i) hp hQ hC hq.le

  have hle : (∑ i ∈ Cᶜ, p i) * k ≤ 1 := by
    by_cases hM : (∑ i, p i * Q i) = 0
    · rw [hM, mul_zero] at hq
      exact absurd rfl hq.ne'
    · have hMpos : 0 < ∑ i, p i * Q i := lt_of_le_of_ne (by
        refine Finset.sum_nonneg ?_
        intro i _
        exact mul_nonneg (hp i) (hQ i)) (Ne.symm hM)
      have hm' : (∑ i ∈ Cᶜ, p i) * k * (∑ i, p i * Q i)
          ≤ 1 * (∑ i, p i * Q i) := by
        calc (∑ i ∈ Cᶜ, p i) * k * (∑ i, p i * Q i)
            = (∑ i ∈ Cᶜ, p i) * (k * ∑ i, p i * Q i) := by ring
          _ ≤ ∑ i, p i * Q i := hm
          _ = 1 * (∑ i, p i * Q i) := by ring
      exact le_of_mul_le_mul_right hm' hMpos
  have heps : (∑ i ∈ Cᶜ, p i) ≤ 1 / k := by
    rw [le_div_iff₀ hk]
    exact hle
  have h2 : 2 * (∑ i ∈ Cᶜ, p i) ≤ 2 * (1 / k) := by linarith [heps]
  have hdiv : 2 * (1 / k) = 2 / k := by ring
  linarith [h2, hdiv]

end Qatlib.Papers.NestedQWalk12.CostModels.AveragingCosts
