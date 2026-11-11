/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.BooleanCubeFourier
import Qatlib.Papers.Trainability23.VarianceScaling.ProductLaws
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Boolean correlation mass bounds

This module bounds Boolean-cube characters and the correlation coefficients `cubeAlpha` of a
finite distribution. It defines `correlationVariance` as a weighted sum of squared nonempty
correlations and bounds it by a power of a scalar base. See [RudolphEtAl2024].

## Main statements

* `cubeAlpha_abs_le_one`: every Boolean correlation has absolute value at most one.
* `cubeAlpha_empty`: the empty correlation equals one.
* `correlationVariance_le`: the weighted correlation sum is at most `((1 - pσ)^2 + pσ^2 / 3)^N`.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Trainability23.VarianceScaling

open scoped BigOperators
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

/-- Every Boolean-cube character has absolute value one. -/
theorem cubeChar_abs {N : ℕ} (S : Finset (Fin N)) (x : Reg N) : |cubeChar S x| = 1 := by
  rw [cubeChar, Finset.abs_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : x i <;> simp [h]

/-- Every Boolean correlation coefficient of a finite distribution has absolute value at most
one. -/
theorem cubeAlpha_abs_le_one {N : ℕ} (p : FinDist (Reg N)) (S : Finset (Fin N)) :
    |cubeAlpha p S| ≤ 1 := by
  have h1 : ∀ x : Reg N, |p.prob x * cubeChar S x| ≤ p.prob x := by
    intro x
    rw [abs_mul, cubeChar_abs, mul_one, abs_of_nonneg (p.nonneg x)]
  calc |cubeAlpha p S| = |∑ x, p.prob x * cubeChar S x| := by rw [cubeAlpha, FinDist.expect]
    _ ≤ ∑ x, |p.prob x * cubeChar S x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, p.prob x := Finset.sum_le_sum fun x _ => h1 x
    _ = 1 := p.sum_one

/-- The square of every Boolean correlation coefficient is at most one. -/
theorem cubeAlpha_sq_le_one {N : ℕ} (p : FinDist (Reg N)) (S : Finset (Fin N)) :
    (cubeAlpha p S) ^ 2 ≤ 1 := by
  have h := abs_le.mp (cubeAlpha_abs_le_one p S)
  nlinarith [h.1, h.2]

/-- The correlation coefficient for the empty set is one. -/
theorem cubeAlpha_empty {N : ℕ} (p : FinDist (Reg N)) : cubeAlpha p ∅ = 1 := by
  simp [cubeAlpha, cubeChar, FinDist.expect, p.sum_one]

/-- The sum over nonempty subsets of squared Boolean correlations weighted by powers of `(1 -
pσ)^2` and `pσ^2 / 3`. -/
noncomputable def correlationVariance {N : ℕ} (p : FinDist (Reg N)) (pσ : ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset.erase ∅,
    ((1 - pσ) ^ 2) ^ (N - S.card) * (pσ ^ 2 / 3) ^ S.card * (cubeAlpha p S) ^ 2

/-- The weighted nonempty correlation sum is at most `((1 - pσ)^2 + pσ^2 / 3)^N`. -/
theorem correlationVariance_le {N : ℕ} (p : FinDist (Reg N)) (pσ : ℝ) :
    correlationVariance p pσ ≤ ((1 - pσ) ^ 2 + pσ ^ 2 / 3) ^ N := by
  have hc : 0 ≤ (1 - pσ) ^ 2 := sq_nonneg _
  have hd : 0 ≤ pσ ^ 2 / 3 := by positivity
  have hw : ∀ S : Finset (Fin N), 0 ≤ ((1 - pσ) ^ 2) ^ (N - S.card) * (pσ ^ 2 / 3) ^ S.card :=
    fun S => mul_nonneg (pow_nonneg hc _) (pow_nonneg hd _)
  have hstep1 : correlationVariance p pσ
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset.erase (∅ : Finset (Fin N)),
          ((1 - pσ) ^ 2) ^ (N - S.card) * (pσ ^ 2 / 3) ^ S.card := by
    unfold correlationVariance
    exact Finset.sum_le_sum fun S _ =>
      mul_le_of_le_one_right (hw S) (cubeAlpha_sq_le_one p S)
  have hstep2 : ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset.erase (∅ : Finset (Fin N)),
        ((1 - pσ) ^ 2) ^ (N - S.card) * (pσ ^ 2 / 3) ^ S.card
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
        ((1 - pσ) ^ 2) ^ (N - S.card) * (pσ ^ 2 / 3) ^ S.card := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun S hS => Finset.mem_of_mem_erase hS) ?_
    intro S _ _
    exact hw S
  calc correlationVariance p pσ
      ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = ((1 - pσ) ^ 2 + pσ ^ 2 / 3) ^ N :=
        sum_powerset_pow_factor N ((1 - pσ) ^ 2) (pσ ^ 2 / 3)

end Qatlib.Papers.Trainability23.VarianceScaling
