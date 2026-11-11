/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Hadamard-test probabilities and sampling bounds

This module models the zero branch of a Hadamard test and its two-outcome probability law for a
normalized vector and a norm-preserving complex operator. It derives the readout expectation,
variance, and sample-average bound used for matrix-element estimation in [Jordan2008a].

## Main statements

* `hadamard_mean`: the real matrix element as a readout expectation.
* `hadamard_variance_le_one`: the readout variance bound.
* `hadamard_sample_bound`: a `1 / (L * ε^2)` deviation bound.

## References

* [Jordan, 2008][Jordan2008a]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.GroupReps08.MainResults.Common

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The zero-outcome branch vector `(ψ + U ψ) / 2` of the Hadamard test. -/
def zeroBranch (U : E →L[ℂ] E) (ψ : E) : E := (1 / 2 : ℂ) • (ψ + U ψ)

/-- The squared norm of the zero-outcome branch vector. -/
def zeroProb (U : E →L[ℂ] E) (ψ : E) : ℝ := ‖zeroBranch U ψ‖ ^ 2

/-- For normalized `ψ` and norm-preserving `U`, the zero-outcome probability equals `(1 + Re ⟪ψ,
U ψ⟫) / 2`. -/
theorem zeroProb_eq (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) :
    zeroProb U ψ = (1 + (⟪ψ, U ψ⟫_ℂ).re) / 2 := by
  have hUψ : ‖U ψ‖ = 1 := by rw [hU, hψ]
  have hnorm : ‖ψ + U ψ‖ ^ 2 = 1 + 2 * (⟪ψ, U ψ⟫_ℂ).re + 1 := by
    rw [norm_add_sq (𝕜 := ℂ), hψ, hUψ]
    simp
  have hcoef : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  unfold zeroProb zeroBranch
  rw [norm_smul, hcoef]
  rw [mul_pow, hnorm]
  ring

/-- The squared norm defining the zero-outcome probability is nonnegative. -/
theorem zeroProb_nonneg (U : E →L[ℂ] E) (ψ : E) : 0 ≤ zeroProb U ψ := by
  unfold zeroProb
  exact sq_nonneg _

/-- For normalized `ψ` and norm-preserving `U`, the zero-outcome probability is at most one. -/
theorem zeroProb_le_one (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : zeroProb U ψ ≤ 1 := by
  rw [zeroProb_eq U ψ hψ hU]
  have hner : ‖⟪ψ, U ψ⟫_ℂ‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) ψ (U ψ)
    rw [hψ, hU ψ, hψ] at this
    simpa using this
  have habs : |(⟪ψ, U ψ⟫_ℂ).re| ≤ 1 := by
    have h := Complex.abs_re_le_norm (⟪ψ, U ψ⟫_ℂ)
    linarith [hner]
  linarith [abs_le.mp habs]

/-- The two-outcome law assigning `zeroProb U ψ` to outcome zero and its complement to outcome
one. -/
def hadamardLaw (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : FinDist (Fin 2) where
  prob i := if i = 0 then zeroProb U ψ else 1 - zeroProb U ψ
  nonneg i := by
    by_cases hi : i = 0
    · simp [hi, zeroProb_nonneg]
    · simp [hi]
      linarith [zeroProb_le_one U ψ hψ hU]
  sum_one := by
    rw [Fin.sum_univ_two]
    simp

/-- The real readout assigning `1` to outcome zero and `-1` to outcome one. -/
def readout : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1

/-- For normalized `ψ` and norm-preserving `U`, the Hadamard readout expectation is the real
part of `⟪ψ, U ψ⟫` [Jordan2008a]. -/
theorem hadamard_mean (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) :
    (hadamardLaw U ψ hψ hU).expect readout = (⟪ψ, U ψ⟫_ℂ).re := by
  rw [FinDist.expect, Fin.sum_univ_two]
  have h0 : (hadamardLaw U ψ hψ hU).prob 0 = zeroProb U ψ := by
    simp [hadamardLaw]
  have h1 : (hadamardLaw U ψ hψ hU).prob 1 = 1 - zeroProb U ψ := by
    simp [hadamardLaw]
  rw [h0, h1]
  simp only [readout]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [if_true, if_neg hne]
  rw [zeroProb_eq U ψ hψ hU]
  ring

/-- The variance of the Hadamard readout equals `4 * zeroProb U ψ * (1 - zeroProb U ψ)`. -/
theorem hadamard_variance (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) :
    (hadamardLaw U ψ hψ hU).variance readout
      = 4 * zeroProb U ψ * (1 - zeroProb U ψ) := by
  unfold FinDist.variance
  rw [FinDist.expect, Fin.sum_univ_two]
  have hmean := hadamard_mean U ψ hψ hU
  have h0 : (hadamardLaw U ψ hψ hU).prob 0 = zeroProb U ψ := by simp [hadamardLaw]
  have h1 : (hadamardLaw U ψ hψ hU).prob 1 = 1 - zeroProb U ψ := by simp [hadamardLaw]
  rw [h0, h1]
  simp only [readout]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [if_true, if_neg hne]
  rw [hmean]

  have hμ : (⟪ψ, U ψ⟫_ℂ).re = 2 * zeroProb U ψ - 1 := by
    rw [zeroProb_eq U ψ hψ hU]; ring
  rw [hμ]
  ring

/-- The Hadamard readout variance is at most one. -/
theorem hadamard_variance_le_one (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) :
    (hadamardLaw U ψ hψ hU).variance readout ≤ 1 := by
  rw [hadamard_variance U ψ hψ hU]
  set p := zeroProb U ψ with hp
  nlinarith [sq_nonneg (2 * p - 1)]

/-- For normalized `ψ`, norm-preserving `U`, and positive `L` and `ε`, the probability that the
sample mean misses the real matrix element by more than `ε` is at most `1 / (L * ε^2)`
[Jordan2008a]. -/
theorem hadamard_sample_bound (U : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1)
    (hU : ∀ x, ‖U x‖ = ‖x‖) (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    FinDist.probEvent (L := L) (hadamardLaw U ψ hψ hU)
        (fun ω => ε < |FinDist.avg readout ω - (⟪ψ, U ψ⟫_ℂ).re|)
      ≤ 1 / (L * ε ^ 2) := by
  have hcheb :=
    FinDist.chebyshev_avg (hadamardLaw U ψ hψ hU) readout hL ε hε
  rw [hadamard_mean U ψ hψ hU] at hcheb
  refine le_trans hcheb ?_
  have hvar := hadamard_variance_le_one U ψ hψ hU
  have hden : (0 : ℝ) ≤ (L : ℝ) * ε ^ 2 := by positivity
  calc (hadamardLaw U ψ hψ hU).variance readout / ((L : ℝ) * ε ^ 2)
      ≤ 1 / ((L : ℝ) * ε ^ 2) :=
        div_le_div_of_nonneg_right hvar hden
    _ = 1 / (L * ε ^ 2) := by ring

end Qatlib.Papers.GroupReps08.MainResults.Common
