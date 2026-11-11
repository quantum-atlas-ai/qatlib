/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki14.MainResults.HaarExpectation.Defs
import Mathlib.Tactic

/-!
# Concentration from uncorrelated overlap moments

This module expands first and second moments of finite real linear combinations and specializes
the second-moment identity to orthogonal families. It derives a concentration bound for
`trotterOverlapExpectation` from the explicitly supplied `UncorrelatedMoments` assumptions and a
zero-sum coefficient condition. See [BabbushEtAl2015].

## Main statements

* `integral_sq_eq_of_orthogonal`: Second moment of an orthogonal finite linear combination.
* `uncorrelated_overlap_concentration`: A probability bound from the supplied overlap moments.

## References

* [Babbush et al., 2015][BabbushEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TrotterSuzuki14.MainResults

open MeasureTheory Finset ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integration commutes with a finite real linear combination of integrable functions. -/
theorem integral_finset_lincomb {κ : Type*} (s : Finset κ) (a : κ → ℝ) (f : κ → Ω → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ ω, ∑ i ∈ s, a i * f i ω ∂μ = ∑ i ∈ s, a i * ∫ ω, f i ω ∂μ := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
  · intro i hi
    exact (hf i hi).const_mul (a i)

/-- When all pairwise products are integrable, the integral of a squared finite linear
combination expands as the sum of its weighted pairwise moments. -/
theorem integral_sq_finset_lincomb {κ : Type*} (s : Finset κ) (a : κ → ℝ) (f : κ → Ω → ℝ)
    (hmul : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => f i ω * f j ω) μ) :
    ∫ ω, (∑ i ∈ s, a i * f i ω) ^ 2 ∂μ
      = ∑ i ∈ s, ∑ j ∈ s, a i * a j * ∫ ω, f i ω * f j ω ∂μ := by
  have hexp : (fun ω => (∑ i ∈ s, a i * f i ω) ^ 2)
      = fun ω => ∑ i ∈ s, ∑ j ∈ s, (a i * a j) * (f i ω * f j ω) := by
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]
    · intro j hj
      exact (hmul i hi j hj).const_mul (a i * a j)
  · intro i hi
    exact integrable_finsetSum _ fun j hj => (hmul i hi j hj).const_mul (a i * a j)

/-- For pairwise orthogonal functions with common second moment `v` and integrable products, a
finite linear combination has second moment `v` times the sum of squared coefficients. -/
theorem integral_sq_eq_of_orthogonal {κ : Type*} [DecidableEq κ] (s : Finset κ) (a : κ → ℝ)
    (g : κ → Ω → ℝ) (v : ℝ)
    (hmul : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => g i ω * g j ω) μ)
    (hsecond : ∀ k, ∫ ω, g k ω ^ 2 ∂μ = v)
    (horth : ∀ k l, k ≠ l → ∫ ω, g k ω * g l ω ∂μ = 0) :
    ∫ ω, (∑ k ∈ s, a k * g k ω) ^ 2 ∂μ = v * ∑ k ∈ s, a k ^ 2 := by
  rw [integral_sq_finset_lincomb s a g hmul]
  have hinner : ∀ i ∈ s, ∑ j ∈ s, a i * a j * ∫ ω, g i ω * g j ω ∂μ = a i * a i * v := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · have hsq_i : ∫ ω, g i ω * g i ω ∂μ = v := by
        simpa [pow_two] using hsecond i
      rw [hsq_i]
    · intro j _ hji
      rw [horth i j (Ne.symm hji)]
      ring
    · intro hi'
      exact absurd hi hi'
  rw [Finset.sum_congr rfl hinner]
  have hcongr : ∀ i ∈ s, a i * a i * v = v * a i ^ 2 := by
    intro i _
    ring
  rw [Finset.sum_congr rfl hcongr]
  exact (Finset.mul_sum s (fun i => a i ^ 2) v).symm

/-- Under `UncorrelatedMoments`, positive dimension, zero-sum coefficients with positive squared
sum, and the stated `MemLp` condition, the event that the absolute overlap is at least `sqrt
(∑ lam²) / (sqrt δ * d)` has measure at most `δ` for `δ > 0`. See [BabbushEtAl2015]. -/
theorem uncorrelated_overlap_concentration
    {d : ℕ} {w : ℕ → Ω → ℝ}
    (hmom : UncorrelatedMoments μ d w) (hd : 1 ≤ d)
    (lam : ℕ → ℝ) (s : Finset ℕ) (hsum : ∑ k ∈ s, lam k = 0)
    (hpos : 0 < ∑ k ∈ s, lam k ^ 2)
    (hmem : MemLp (trotterOverlapExpectation lam w s) 2 μ)
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | Real.sqrt (∑ k ∈ s, lam k ^ 2) / (Real.sqrt δ * (d : ℝ))
        ≤ |trotterOverlapExpectation lam w s ω|} ≤ ENNReal.ofReal δ := by
  haveI := hmom.isProb
  set S : ℝ := ∑ k ∈ s, lam k ^ 2 with hSdef
  set V : ℝ := 2 / ((d : ℝ) * ((d : ℝ) + 1)) - 1 / (d : ℝ) ^ 2 with hVdef
  set cc : ℝ := Real.sqrt S / (Real.sqrt δ * (d : ℝ)) with hcc
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hS_pos : 0 < S := by rw [hSdef]; exact hpos

  have hXeq : ∀ ω, trotterOverlapExpectation lam w s ω
      = ∑ k ∈ s, lam k * centeredOverlap w d k ω := by
    intro ω
    have hsplit : ∑ k ∈ s, lam k * w k ω
        = (∑ k ∈ s, lam k * centeredOverlap w d k ω)
            + (∑ k ∈ s, lam k) * (1 / (d : ℝ)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by unfold centeredOverlap; ring
    unfold trotterOverlapExpectation
    rw [hsplit, hsum, zero_mul, add_zero]

  have hmean0 : ∫ ω, trotterOverlapExpectation lam w s ω ∂μ = 0 := by
    have hcongr : ∫ ω, trotterOverlapExpectation lam w s ω ∂μ
        = ∫ ω, ∑ k ∈ s, lam k * centeredOverlap w d k ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω using hXeq ω
    rw [hcongr, integral_finset_lincomb s lam (centeredOverlap w d)
      (fun k _ => hmom.int_centered k)]
    simp [hmom.centered_mean]

  have hsq : ∫ ω, trotterOverlapExpectation lam w s ω ^ 2 ∂μ = V * S := by
    have hcongr : ∫ ω, trotterOverlapExpectation lam w s ω ^ 2 ∂μ
        = ∫ ω, (∑ k ∈ s, lam k * centeredOverlap w d k ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω using by rw [hXeq ω]
    rw [hcongr]
    have hmain := integral_sq_eq_of_orthogonal s lam (centeredOverlap w d) V
      (fun i _ j _ => hmom.int_centered_mul i j)
      (fun k => hmom.centered_second k)
      (fun k l hkl => hmom.centered_orth k l hkl)
    rw [hmain, hSdef]
  have hvar : variance (trotterOverlapExpectation lam w s) μ = V * S := by
    rw [variance_of_integral_eq_zero hmem.aemeasurable hmean0]
    exact hsq

  have hV_le : V ≤ 1 / (d : ℝ) ^ 2 := by
    rw [hVdef, sub_le_iff_le_add]
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have hprod : (d : ℝ) ^ 2 ≤ (d : ℝ) * ((d : ℝ) + 1) := by nlinarith
    have h1 : 2 / ((d : ℝ) * ((d : ℝ) + 1)) ≤ 2 / (d : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) hd2 hprod
    calc 2 / ((d : ℝ) * ((d : ℝ) + 1)) ≤ 2 / (d : ℝ) ^ 2 := h1
      _ = 1 / (d : ℝ) ^ 2 + 1 / (d : ℝ) ^ 2 := by ring

  have hcc_pos : 0 < cc := by
    rw [hcc]
    exact div_pos (Real.sqrt_pos.mpr hS_pos) (mul_pos (Real.sqrt_pos.mpr hδ) hd_pos)
  have hcc_sq : cc ^ 2 = S / (δ * (d : ℝ) ^ 2) := by
    rw [hcc, div_pow, Real.sq_sqrt hS_pos.le, mul_pow, Real.sq_sqrt hδ.le]
  have hcheb := meas_ge_le_variance_div_sq hmem hcc_pos
  have hcheb' : μ {ω | cc ≤ |trotterOverlapExpectation lam w s ω|} ≤
      ENNReal.ofReal (variance (trotterOverlapExpectation lam w s) μ / cc ^ 2) := by
    simpa [hmean0] using hcheb
  have hratio : variance (trotterOverlapExpectation lam w s) μ / cc ^ 2 ≤ δ := by
    rw [hvar, hcc_sq]
    have hSne : S ≠ 0 := ne_of_gt hS_pos
    have hdens : (0 : ℝ) < δ * (d : ℝ) ^ 2 := by positivity
    have hD : δ * (d : ℝ) ^ 2 ≠ 0 := ne_of_gt hdens
    have hstep : V * S / (S / (δ * (d : ℝ) ^ 2)) = V * δ * (d : ℝ) ^ 2 := by
      field_simp
    rw [hstep]
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have hVd : V ≤ 1 / (d : ℝ) ^ 2 := hV_le
    have hVS : V * δ * (d : ℝ) ^ 2 ≤ (1 / (d : ℝ) ^ 2) * δ * (d : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hd2.le
      exact mul_le_mul_of_nonneg_right hVd hδ.le
    have hcollapse : (1 / (d : ℝ) ^ 2) * δ * (d : ℝ) ^ 2 = δ := by
      have hd2ne : (d : ℝ) ^ 2 ≠ 0 := ne_of_gt hd2
      field_simp
    linarith
  calc μ {ω | cc ≤ |trotterOverlapExpectation lam w s ω|}
      ≤ ENNReal.ofReal (variance (trotterOverlapExpectation lam w s) μ / cc ^ 2) := hcheb'
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hratio

end Qatlib.Papers.TrotterSuzuki14.MainResults
