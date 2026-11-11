/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Variance estimates for metrology

This module develops finite distribution variance bounds in terms of the half width
`spectralSpread`. It defines the balanced two point law, computes its extremal variance, and
supplies the scalar step from a spread bound to an error inequality. See
[GiovannettiLloydMaccone2006].

## Main statements

* `variance_le_spread_sq`: A real observable taking values in `[a, b]` has variance at most
  `spectralSpread a b ^ 2`.
* `twoPointLaw_variance`: The balanced two point observable has variance `spectralSpread a b ^
  2`.
* `error_ge_of_variance_bound`: If positive `Δh ≤ R` and `δφ * Δh ≥ 1 / (2 * √ν)` for positive
  `ν`, then `δφ ≥ 1 / (2 * √ν * R)`.

## References

* [Giovannetti et al., 2006][GiovannettiLloydMaccone2006]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.Source

/-- The half width `(b - a) / 2` of a spectral interval. -/
def spectralSpread (a b : ℝ) : ℝ := (b - a) / 2

/-- The spectral spread of `[a, b]` equals `(b - a) / 2`. -/
@[simp] theorem spectralSpread_def (a b : ℝ) : spectralSpread a b = (b - a) / 2 := rfl

/-- The expectation of `(f - c) ^ 2` equals the second moment of `f` minus twice `c` times its
mean plus `c ^ 2`. -/
theorem expect_shift_sq {X : Type} [Fintype X] (p : FinDist X) (f : X → ℝ) (c : ℝ) :
    p.expect (fun x => (f x - c) ^ 2)
      = p.expect (fun x => (f x) ^ 2) - 2 * c * p.expect f + c ^ 2 := by
  simp only [FinDist.expect]
  have h1 : ∀ x : X, p.prob x * (f x - c) ^ 2
      = p.prob x * (f x) ^ 2 - (2 * c) * (p.prob x * f x) + c ^ 2 * p.prob x :=
    fun x => by ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h2 : (∑ x, (2 * c) * (p.prob x * f x)) = (2 * c) * (∑ x, p.prob x * f x) := by
    rw [Finset.mul_sum]
  have h3 : (∑ x, c ^ 2 * p.prob x) = c ^ 2 * (∑ x, p.prob x) := by
    rw [Finset.mul_sum]
  rw [h2, h3, p.sum_one, mul_one]

/-- A real observable taking values in `[a, b]` has variance at most `spectralSpread a b ^ 2`.
See [GiovannettiLloydMaccone2006]. -/
theorem variance_le_spread_sq {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) {a b : ℝ}
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) :
    p.variance f ≤ spectralSpread a b ^ 2 := by
  set c : ℝ := (a + b) / 2 with hc
  have hshift : p.variance f
      = p.expect (fun x => (f x - c) ^ 2) - (p.expect f - c) ^ 2 := by
    rw [FinDist.variance_eq_expect_sq_sub p f, expect_shift_sq p f c]
    ring
  rw [hshift]
  have hle : p.expect (fun x => (f x - c) ^ 2) ≤ spectralSpread a b ^ 2 := by
    simp only [FinDist.expect]
    calc ∑ x, p.prob x * (f x - c) ^ 2
        ≤ ∑ x, p.prob x * spectralSpread a b ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (p.nonneg x)
          have h1 : -(spectralSpread a b) ≤ f x - c := by
            simp only [spectralSpread, hc]; linarith [ha x]
          have h2 : f x - c ≤ spectralSpread a b := by
            simp only [spectralSpread, hc]; linarith [hb x]
          exact sq_le_sq' h1 h2
      _ = spectralSpread a b ^ 2 := by
          rw [← Finset.sum_mul, p.sum_one, one_mul]
  have hnon : 0 ≤ (p.expect f - c) ^ 2 := sq_nonneg _
  linarith

/-- For a nonnegative spectral spread, the standard deviation of an observable in `[a, b]` is at
most that spread. -/
theorem sqrt_variance_le_spread {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) {a b : ℝ}
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) (hspread : 0 ≤ spectralSpread a b) :
    Real.sqrt (p.variance f) ≤ spectralSpread a b := by
  rw [Real.sqrt_le_iff]
  exact ⟨hspread, variance_le_spread_sq p f ha hb⟩

/-- The uniform finite probability distribution on two outcomes. -/
def twoPointLaw : FinDist (Fin 2) where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by
    rw [Fin.sum_univ_two]; norm_num

/-- Each outcome of `twoPointLaw` has probability one half. -/
@[simp] theorem twoPointLaw_prob (x : Fin 2) : twoPointLaw.prob x = 1 / 2 := rfl

/-- The observable on `Fin 2` with values `a` at zero and `b` at one. -/
def twoPointValue (a b : ℝ) : Fin 2 → ℝ := ![a, b]

/-- The balanced two point observable has variance `spectralSpread a b ^ 2`. -/
theorem twoPointLaw_variance (a b : ℝ) :
    twoPointLaw.variance (twoPointValue a b) = spectralSpread a b ^ 2 := by
  rw [FinDist.variance_eq_expect_sq_sub]
  simp only [FinDist.expect, twoPointLaw_prob, twoPointValue, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    spectralSpread]
  ring

/-- A sum of `N` real numbers from `[a, b]` lies in `[N * a, N * b]`. -/
theorem spectralSumBounds {N : ℕ} (f : Fin N → ℝ) {a b : ℝ}
    (ha : ∀ j, a ≤ f j) (hb : ∀ j, f j ≤ b) :
    (N : ℝ) * a ≤ ∑ j, f j ∧ ∑ j, f j ≤ (N : ℝ) * b := by
  constructor
  · have hsum : (∑ _j : Fin N, a) = (N : ℝ) * a := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hsum]
    exact Finset.sum_le_sum fun j _ => ha j
  · have hsum : (∑ _j : Fin N, b) = (N : ℝ) * b := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hsum]
    exact Finset.sum_le_sum fun j _ => hb j

/-- The variance of any real observable under a finite probability distribution is nonnegative. -/
theorem variance_nonneg {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) : 0 ≤ p.variance f := by
  rw [FinDist.variance]
  simp only [FinDist.expect]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg _)

/-- If positive `Δh ≤ R` and `δφ * Δh ≥ 1 / (2 * √ν)` for positive `ν`, then `δφ ≥ 1 / (2 * √ν *
R)`. -/
theorem error_ge_of_variance_bound {δφ Δh R ν : ℝ}
    (hν : 0 < ν) (hΔh : 0 < Δh) (hR : 0 < R) (hΔhR : Δh ≤ R)
    (hcr : δφ * Δh ≥ 1 / (2 * Real.sqrt ν)) :
    δφ ≥ 1 / (2 * Real.sqrt ν * R) := by
  set c : ℝ := 1 / (2 * Real.sqrt ν) with hc
  have hcpos : 0 < c := by
    rw [hc]; positivity
  have hδ : c / Δh ≤ δφ := by
    rw [div_le_iff₀ hΔh]
    have : c ≤ δφ * Δh := hcr
    linarith
  have hdiv : c / R ≤ c / Δh := by
    rw [div_le_div_iff₀ hR hΔh]
    nlinarith
  have := le_trans hdiv hδ
  have hden : 1 / (2 * Real.sqrt ν * R) = c / R := by
    rw [hc, div_div]
  rw [hden]
  exact this

end Qatlib.Papers.QuantumMetro05.MainResults.Source
