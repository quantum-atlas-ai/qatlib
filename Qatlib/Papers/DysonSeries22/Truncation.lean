/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DysonSeries22.ExactSource
import Qatlib.Foundations.TimeEvolution.DysonError.SeriesSteps
import Qatlib.Foundations.TimeEvolution.DysonError.FactorialTail
import Qatlib.Papers.DysonSeries22.PureDistance

/-!
# Truncated Dyson solutions and error bounds

`truncatedEvolution`, `truncatedSource`, and `truncatedSolution` give finite Dyson
approximations for a driven linear equation. This module bounds evolution and source truncation
errors by factorial tails and exponential majorants, and combines them into an error bound for a
solution with continuous coefficients.

The mathematical setting follows [BerryCosta2024].

## Main statements

* `evolution_error_factorial`: a factorial and exponential bound for homogeneous truncation.
* `source_error_factorial`: the corresponding bound for the driving contribution.
* `solution_error_le`: the total solution error splits into evolution and source errors.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
namespace Qatlib.Papers.DysonSeries22.Truncation
open Matrix Set
open scoped Matrix.Norms.L2Operator Topology
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.DysonSeries22.ExactSource
open Qatlib.Foundations.TimeEvolution.DysonError
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sum of the ordered Dyson evolution terms indexed from zero through `K`. -/
def truncatedEvolution (A : ℝ → Matrix I I ℂ) (s t : ℝ) (K : ℕ) : Matrix I I ℂ :=
  ∑ n ∈ Finset.range (K+1), orderedDysonTerm (fun u => -A u) s n t

/-- The Euclidean sum of the first `K` Dyson source terms. -/
def truncatedSource (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K : ℕ) : EuclideanSpace ℂ I :=
  ∑ n ∈ Finset.range K, toEuclidean_fromVec (dysonSourceTerm A b s n t)

/-- The truncated evolution applied to the initial state, plus the truncated source
contribution. -/
def truncatedSolution (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (x₀ : QState I) (s t : ℝ) (K : ℕ) : EuclideanSpace ℂ I :=
  toEuclidean_fromVec (truncatedEvolution A s t K *ᵥ x₀) + truncatedSource A b s t K

/-- A uniform matrix norm bound gives an evolution truncation error bounded by the factorial
tail starting at order `K + 1`. -/
theorem evolution_error_le (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (s t M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M) (K : ℕ) :
    ‖orderedEvolution (fun u => -A u) s t - truncatedEvolution A s t K‖ ≤
      ∑' n : ℕ, (M*|t-s|)^(n+(K+1)) / ((n+(K+1)).factorial : ℝ) := by
  apply truncation_error_le _ _ (Real.summable_pow_div_factorial _) _ (K+1)
  intro n
  exact orderedDysonTerm_norm_le _ hA.neg s t M hM (by simpa using! hbound) n

/-- Uniform bounds on the continuous matrix and driving terms give a source truncation error
bounded by the stated factorial tail starting at source index `K`. -/
theorem source_error_le (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t M C : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hboundA : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M)
    (hboundb : ∀ u ∈ uIcc s t, ‖toEuclidean_fromVec (b u)‖ ≤ C) (K : ℕ) :
    ‖toEuclidean_fromVec (dysonSourceSeries A b s t) - truncatedSource A b s t K‖ ≤
      ∑' n : ℕ, C*|t-s| *(M*|t-s|)^(n+K) / ((n+K+1).factorial : ℝ) := by
  have hg : Summable (fun n : ℕ => C*|t-s| *(M*|t-s|)^n / ((n+1).factorial : ℝ)) := by
    have hs : Summable (fun n : ℕ => (M*|t-s|)^n / ((n+1).factorial : ℝ)) := by
      apply Summable.of_nonneg_of_le (fun n => by positivity) _
        (Real.summable_pow_div_factorial (M*|t-s|))
      intro n
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
    simpa only [mul_div_assoc] using! hs.mul_left (C*|t-s|)
  have h := truncation_error_le (fun n => toEuclidean_fromVec (dysonSourceTerm A b s n t))
    _ hg (dysonSourceTerm_norm_le A b hA hb s t M C hM hC hboundA hboundb) K
  let e : QState I ≃L[ℂ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm
  have he : toEuclidean_fromVec (dysonSourceSeries A b s t) =
      ∑' n, toEuclidean_fromVec (dysonSourceTerm A b s n t) :=
    (e : QState I →L[ℂ] EuclideanSpace ℂ I).map_tsum (dysonSourceTerm_summable A b hA hb s t)
  simpa only [he,truncatedSource] using! h

/-- With matrix norm bounded by `M`, the evolution truncation error is at most `(M * |t - s|)^(K
+ 1) / (K + 1)!` times `exp (M * |t - s|)`. See [Berry and Costa, 2024, Eqs.
(5)–(7)][BerryCosta2024]. -/
theorem evolution_error_factorial (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    (s t M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M) (K : ℕ) :
    ‖orderedEvolution (fun u => -A u) s t - truncatedEvolution A s t K‖ ≤
      (M*|t-s|)^(K+1) / ((K+1).factorial:ℝ) * Real.exp (M*|t-s|) :=
  (evolution_error_le A hA s t M hM hbound K).trans
    (factorial_tail_le _ (mul_nonneg hM (abs_nonneg _)) (K+1))

/-- Uniform matrix and driving bounds give source truncation error at most `C * |t - s| * (M *
|t - s|)^K / (K + 1)!` times `exp (M * |t - s|)`. See [Berry and Costa, 2024, Eqs.
(12)–(14)][BerryCosta2024]. -/
theorem source_error_factorial (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t M C : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hboundA : ∀ u ∈ uIcc s t, ‖A u‖ ≤ M)
    (hboundb : ∀ u ∈ uIcc s t, ‖toEuclidean_fromVec (b u)‖ ≤ C) (K : ℕ) :
    ‖toEuclidean_fromVec (dysonSourceSeries A b s t) - truncatedSource A b s t K‖ ≤
      C*|t-s| * ((M*|t-s|)^K / ((K+1).factorial:ℝ) * Real.exp (M*|t-s|)) := by
  refine (source_error_le A b hA hb s t M C hM hC hboundA hboundb K).trans ?_
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    (shifted_factorial_tail_le (M*|t-s|) (mul_nonneg hM (abs_nonneg _)) K 1)
    (mul_nonneg hC (abs_nonneg _))

/-- The difference of two affine matrix outputs is bounded by the matrix difference norm times
the input norm plus the difference of the additive terms. -/
theorem output_error_le (W V : Matrix I I ℂ) (u q : QState I)
    (v : EuclideanSpace ℂ I) :
    ‖toEuclidean_fromVec (W *ᵥ u + q) - (toEuclidean_fromVec (V *ᵥ u) + v)‖ ≤
      ‖W-V‖ * ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec q-v‖ := by
  let e : QState I ≃L[ℂ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm
  change ‖e (W *ᵥ u + q) - (e (V *ᵥ u) + v)‖ ≤ _
  rw [map_add]
  have h : e (W *ᵥ u) + e q - (e (V *ᵥ u) + v) =
      e ((W-V) *ᵥ u) + (e q-v) := by
    rw [Matrix.sub_mulVec,map_sub]
    abel
  rw [h]
  have hm : ‖e ((W-V) *ᵥ u)‖ ≤ ‖W-V‖ * ‖toEuclidean_fromVec u‖ :=
    norm_mulVec_le (W-V) u
  exact (norm_add_le _ _).trans (add_le_add hm (le_refl _))

/-- For an exact solution with continuous coefficients, the truncated solution error is bounded
by the evolution error times the initial norm plus the source error. See [Berry and Costa,
2024, Eqs. (12)–(14)][BerryCosta2024]. -/
theorem solution_error_le (A : ℝ → Matrix I I ℂ) (b x : ℝ → QState I)
    (hA : Continuous A) (hb : Continuous b) (s t : ℝ)
    (hx : ∀ u, HasDerivAt x (A u *ᵥ x u + b u) u) (K : ℕ) :
    ‖toEuclidean_fromVec (x t) - truncatedSolution A b (x s) s t K‖ ≤
      ‖orderedEvolution (fun u => -A u) s t - truncatedEvolution A s t K‖ *
        ‖toEuclidean_fromVec (x s)‖ +
      ‖toEuclidean_fromVec (dysonSourceSeries A b s t) - truncatedSource A b s t K‖ := by
  have h := output_error_le (orderedEvolution (fun u => -A u) s t)
    (truncatedEvolution A s t K) (x s) (dysonSourceSeries A b s t)
    (truncatedSource A b s t K)
  have hxrep := congrFun (solution_eq_initial_add_dyson A b x hA hb s hx) t
  rw [← hxrep] at h
  exact h
end Qatlib.Papers.DysonSeries22.Truncation
