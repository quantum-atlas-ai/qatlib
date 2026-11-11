/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.StatDistance
import Qatlib.Papers.AdiabStateGen03.MainResults.SZKReduction.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# From statistical distance to amplitude tests

This module defines `SDReduction` using close and far pairs of probability distributions and
defines `AmplitudeTestable` through distances between their square-root states. The theorem
`amplitudeTestable_of_sd` converts these statistical-distance thresholds to amplitude-distance
thresholds, using `amplitude_close_of_tv` and `amplitude_far_of_tv`. The mathematical context is
[AharonovTaShma2007].

## Main statements

* `amplitude_close_of_tv`: Probability distributions at total variation distance at most `1 / 3`
  have square-root states at norm distance at most `Real.sqrt (2 / 3)`.
* `amplitudeTestable_of_sd`: A statistical-distance reduction supplies an amplitude test with
  the specified close and far thresholds.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.SZKReduction

open Qatlib.Papers.AdiabStateGen03.MainResults
open WithLp

variable {m : ℕ}

/-- The square-root distribution state is the Euclidean vector of real square roots, embedded in
the complex numbers. -/
lemma ketOfDist_eq_toLp (π : Dim m → ℝ) :
    ketOfDist π = toLp 2 (fun i => (Real.sqrt (π i) : ℂ)) := rfl

/-- The squared norm of the difference of two square-root states equals the sum of squared
differences of their real amplitudes [AharonovTaShma2007]. -/
theorem norm_ketOfDist_sub_sq (p q : Dim m → ℝ) :
    ‖ketOfDist p - ketOfDist q‖ ^ 2
      = ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
  rw [ketOfDist_eq_toLp p, ketOfDist_eq_toLp q, ← WithLp.toLp_sub,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [PiLp.toLp_apply, Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Probability distributions at total variation distance at most `1 / 3` have square-root
states at norm distance at most `Real.sqrt (2 / 3)` [AharonovTaShma2007]. -/
theorem amplitude_close_of_tv (p q : Dim m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (h : (1 / 2) * ∑ i, |p i - q i| ≤ 1 / 3) :
    ‖ketOfDist p - ketOfDist q‖ ≤ Real.sqrt (2 / 3) := by
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
  rw [norm_ketOfDist_sub_sq]
  have hsum := sum_sq_sub_sqrt_le_of_tv p q hp hq hp1 hq1 (1 / 3) h
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  linarith

/-- Probability distributions at total variation distance at least `2 / 3` have square-root
states at norm distance at least `2 / 3` [AharonovTaShma2007]. -/
theorem amplitude_far_of_tv (p q : Dim m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (h : 2 / 3 ≤ (1 / 2) * ∑ i, |p i - q i|) :
    2 / 3 ≤ ‖ketOfDist p - ketOfDist q‖ := by
  have htv := StatDistance.tv_le_sqrt_sum_sq_sub_sqrt p q hp hq hp1 hq1
  have hss : (2 / 3 : ℝ)
      ≤ Real.sqrt (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) :=
    le_trans h htv
  have hsq : (2 / 3 : ℝ) ^ 2 ≤ ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 := by
    have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) (Real.sqrt_nonneg _)).mpr hss
    rwa [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at hs
  rw [← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) (norm_nonneg _)]
  rw [norm_ketOfDist_sub_sq]
  exact hsq

/-- A pair of probability-distribution families separating the Boolean outcomes of a promise
problem by total variation thresholds `1 / 3` and `2 / 3`. -/
structure SDReduction (L : PromiseProblem) where

  bits : ℕ

  p : List Bool → Dim bits → ℝ

  q : List Bool → Dim bits → ℝ

  p_prob : ∀ x, (∀ i, 0 ≤ p x i) ∧ ∑ i, p x i = 1

  q_prob : ∀ x, (∀ i, 0 ≤ q x i) ∧ ∑ i, q x i = 1

  close_yes : ∀ x, L.decide x = true →
    (1 / 2) * ∑ i, |p x i - q x i| ≤ 1 / 3

  far_no : ∀ x, L.decide x = false →
    2 / 3 ≤ (1 / 2) * ∑ i, |p x i - q x i|

/-- The existence of weight families whose square-root states have distance at most `Real.sqrt
(2 / 3)` on true inputs and at least `2 / 3` on false inputs. -/
def AmplitudeTestable (L : PromiseProblem) : Prop :=
  ∃ (bits : ℕ) (p q : List Bool → Dim bits → ℝ),
    (∀ x, L.decide x = true → ‖ketOfDist (p x) - ketOfDist (q x)‖ ≤ Real.sqrt (2 / 3)) ∧
    (∀ x, L.decide x = false → 2 / 3 ≤ ‖ketOfDist (p x) - ketOfDist (q x)‖)

/-- A statistical-distance reduction supplies an amplitude test with the specified close and far
thresholds. -/
theorem amplitudeTestable_of_sd {L : PromiseProblem} (R : SDReduction L) :
    AmplitudeTestable L := by
  refine ⟨R.bits, R.p, R.q, ?_, ?_⟩
  · intro x hx
    exact amplitude_close_of_tv (R.p x) (R.q x) (R.p_prob x).1 (R.q_prob x).1
      (R.p_prob x).2 (R.q_prob x).2 (R.close_yes x hx)
  · intro x hx
    exact amplitude_far_of_tv (R.p x) (R.q x) (R.p_prob x).1 (R.q_prob x).1
      (R.p_prob x).2 (R.q_prob x).2 (R.far_no x hx)

end Qatlib.Papers.AdiabStateGen03.MainResults.SZKReduction
