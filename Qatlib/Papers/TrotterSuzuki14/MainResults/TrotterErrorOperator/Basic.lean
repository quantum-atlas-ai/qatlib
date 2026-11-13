/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki14.MainResults.TrotterErrorOperator.Defs
import Mathlib.Tactic

/-!
# Norm bounds for the leading second-order Trotter error

This module bounds `leadingSecondOrderError` using a disjoint cover of its nested-commutator
triples by two classes with operator bounds proportional to `Z²` and `Z`. Cardinality bounds for
these classes give a uniform estimate proportional to `N⁴ Z⁶ + N¹⁰ Z³` for fixed time step and
operator constant. See [BabbushEtAl2015].

## Main statements

* `leadingSecondOrderError_norm_le`: Explicit cardinality-dependent norm estimate.
* `leadingSecondOrderError_norm_bigO`: Uniform bound from polynomial triple counts.

## References

* [Babbush et al., 2015][BabbushEtAl2015]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TrotterSuzuki14.MainResults

open Finset
open scoped BigOperators

variable {ι A : Type*}

section NormBound

variable [NormedRing A] [NormedSpace ℝ A] [DecidableEq ι]

/-- For a disjoint cover of triples whose factors are bounded by `c Z²` or `c Z`, the
leading-error norm is at most `(Δt² / 12) * 4 c³ * (oneBody.card * Z⁶ + twoBody.card * Z³)`
when `c` and `Z` are nonnegative. -/
theorem leadingSecondOrderError_norm_le
    (op : ι → A) (triples oneBody twoBody : Finset (Triple ι)) (Δt : ℝ)
    {c Z : ℝ} (hc : 0 ≤ c) (hZ : 0 ≤ Z)
    (hcover : triples ⊆ oneBody ∪ twoBody)
    (hdisj : Disjoint oneBody twoBody)
    (h₁ : ∀ t ∈ oneBody,
      ‖op t.1‖ ≤ c * Z ^ 2 ∧ ‖op t.2.1‖ ≤ c * Z ^ 2 ∧ ‖op t.2.2‖ ≤ c * Z ^ 2)
    (h₂ : ∀ t ∈ twoBody,
      ‖op t.1‖ ≤ c * Z ∧ ‖op t.2.1‖ ≤ c * Z ∧ ‖op t.2.2‖ ≤ c * Z) :
    ‖leadingSecondOrderError op triples Δt‖ ≤
      (Δt ^ 2 / 12) * (4 * c ^ 3) *
        ((oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3) := by

  have hS : ‖∑ t ∈ triples, suzukiWeight t.1 t.2.1 • tripleProduct op t‖
      ≤ 4 * c ^ 3 * ((oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3) := by
    calc ‖∑ t ∈ triples, suzukiWeight t.1 t.2.1 • tripleProduct op t‖
        ≤ ∑ t ∈ triples, ‖suzukiWeight t.1 t.2.1 • tripleProduct op t‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ triples, ‖tripleProduct op t‖ := by
          apply sum_le_sum
          intro t _
          rw [norm_smul, Real.norm_eq_abs]
          have hw : |suzukiWeight t.1 t.2.1| ≤ 1 := abs_suzukiWeight_le_one t.1 t.2.1
          have hn : 0 ≤ ‖tripleProduct op t‖ := norm_nonneg _
          nlinarith
      _ ≤ ∑ t ∈ oneBody ∪ twoBody, ‖tripleProduct op t‖ := by
          apply sum_le_sum_of_subset_of_nonneg hcover
          intro t _ _
          exact norm_nonneg _
      _ = ∑ t ∈ oneBody, ‖tripleProduct op t‖ + ∑ t ∈ twoBody, ‖tripleProduct op t‖ :=
          sum_union hdisj
      _ ≤ ∑ _t ∈ oneBody, 4 * c ^ 3 * Z ^ 6 + ∑ _t ∈ twoBody, 4 * c ^ 3 * Z ^ 3 := by
          apply add_le_add
          · apply sum_le_sum
            intro t ht
            exact tripleProduct_norm_le_of_oneBody op t (h₁ t ht).1 (h₁ t ht).2.1
              (h₁ t ht).2.2 hc
          · apply sum_le_sum
            intro t ht
            exact tripleProduct_norm_le_of_twoBody op t (h₂ t ht).1 (h₂ t ht).2.1
              (h₂ t ht).2.2 hc hZ
      _ = 4 * c ^ 3 * ((oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3) := by
          rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
          ring

  have hfac : ‖(-(Δt ^ 2 / 12) : ℝ)‖ = Δt ^ 2 / 12 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  calc ‖leadingSecondOrderError op triples Δt‖
      = (Δt ^ 2 / 12) *
          ‖∑ t ∈ triples, suzukiWeight t.1 t.2.1 • tripleProduct op t‖ := by
        unfold leadingSecondOrderError
        rw [norm_smul, hfac]
    _ ≤ (Δt ^ 2 / 12) *
          (4 * c ^ 3 * ((oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (Δt ^ 2 / 12) * (4 * c ^ 3) *
          ((oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3) := by ring

/-- For fixed operators, time step, and positive `c`, there is a positive constant bounding the
leading-error norm by `C * (N⁴ Z⁶ + N¹⁰ Z³)` under the stated disjoint-cover, factor-norm,
and cardinality hypotheses. See [BabbushEtAl2015]. -/
theorem leadingSecondOrderError_norm_bigO
    (op : ι → A) (Δt : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (triples oneBody twoBody : Finset (Triple ι)) (N : ℕ) (Z : ℝ),
        0 ≤ Z →
        triples ⊆ oneBody ∪ twoBody →
        Disjoint oneBody twoBody →
        (∀ t ∈ oneBody,
          ‖op t.1‖ ≤ c * Z ^ 2 ∧ ‖op t.2.1‖ ≤ c * Z ^ 2 ∧ ‖op t.2.2‖ ≤ c * Z ^ 2) →
        (∀ t ∈ twoBody,
          ‖op t.1‖ ≤ c * Z ∧ ‖op t.2.1‖ ≤ c * Z ∧ ‖op t.2.2‖ ≤ c * Z) →
        oneBody.card ≤ N ^ 4 →
        twoBody.card ≤ N ^ 10 →
        ‖leadingSecondOrderError op triples Δt‖ ≤
          C * ((N : ℝ) ^ 4 * Z ^ 6 + (N : ℝ) ^ 10 * Z ^ 3) := by
  refine ⟨(Δt ^ 2 / 12) * (4 * c ^ 3) + 1, by positivity, ?_⟩
  intro triples oneBody twoBody N Z hZ hcover hdisj h₁ h₂ hc1 hc2
  have hmain := leadingSecondOrderError_norm_le op triples oneBody twoBody Δt
    hc.le hZ hcover hdisj h₁ h₂
  have hc1' : (oneBody.card : ℝ) ≤ (N : ℝ) ^ 4 := by exact_mod_cast hc1
  have hc2' : (twoBody.card : ℝ) ≤ (N : ℝ) ^ 10 := by exact_mod_cast hc2
  have hZ6 : 0 ≤ Z ^ 6 := by positivity
  have hZ3 : 0 ≤ Z ^ 3 := by positivity
  have hN4 : (0 : ℝ) ≤ (N : ℝ) ^ 4 := by positivity
  have hN10 : (0 : ℝ) ≤ (N : ℝ) ^ 10 := by positivity
  have hcard : (oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3
      ≤ (N : ℝ) ^ 4 * Z ^ 6 + (N : ℝ) ^ 10 * Z ^ 3 := by
    have h1 : (oneBody.card : ℝ) * Z ^ 6 ≤ (N : ℝ) ^ 4 * Z ^ 6 :=
      mul_le_mul_of_nonneg_right hc1' hZ6
    have h2 : (twoBody.card : ℝ) * Z ^ 3 ≤ (N : ℝ) ^ 10 * Z ^ 3 :=
      mul_le_mul_of_nonneg_right hc2' hZ3
    linarith
  have hnonneg : 0 ≤ (N : ℝ) ^ 4 * Z ^ 6 + (N : ℝ) ^ 10 * Z ^ 3 := by
    have := mul_nonneg hN4 hZ6
    have := mul_nonneg hN10 hZ3
    linarith
  have hstep : (Δt ^ 2 / 12) * (4 * c ^ 3) *
        ((oneBody.card : ℝ) * Z ^ 6 + (twoBody.card : ℝ) * Z ^ 3)
      ≤ ((Δt ^ 2 / 12) * (4 * c ^ 3) + 1) *
        ((N : ℝ) ^ 4 * Z ^ 6 + (N : ℝ) ^ 10 * Z ^ 3) := by
    have hbase : (Δt ^ 2 / 12) * (4 * c ^ 3) * ((oneBody.card : ℝ) * Z ^ 6
          + (twoBody.card : ℝ) * Z ^ 3)
        ≤ (Δt ^ 2 / 12) * (4 * c ^ 3) *
          ((N : ℝ) ^ 4 * Z ^ 6 + (N : ℝ) ^ 10 * Z ^ 3) := by
      apply mul_le_mul_of_nonneg_left hcard
      positivity
    nlinarith [hbase, hnonneg]
  linarith [hmain, hstep]

end NormBound

end Qatlib.Papers.TrotterSuzuki14.MainResults
