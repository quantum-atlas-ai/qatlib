/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDistTV
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Maximal coupling of finite distributions

This module constructs a joint law from the common mass and disjoint residual masses of two
finite distributions. `coupling_row` and `coupling_col` establish its marginals, and
`coupling_mismatch` identifies its disagreement probability with total variation. The
construction realizes a classical statistical distance discussed in [Watrous2018].

## Main statements

* `residualMass_eq_tvDist`: The total residual mass equals the total variation distance `tvDist
  p q`.
* `coupling`: The finite joint distribution formed from diagonal common mass and the normalized
  product of residual masses.
* `coupling_mismatch`: The probability that the two coordinates of the constructed coupling
  differ equals `tvDist p q`.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteMaximalCoupling

noncomputable section

variable {J : Type*} [Fintype J]

/-- The pointwise minimum of the probability masses of `p` and `q`. -/
def commonMass (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) : ℝ :=
    min (p.prob i) (q.prob i)

/-- The mass of `p` remaining after removing its pointwise common mass with `q`. -/
def leftResidual (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) : ℝ :=
    p.prob i - commonMass p q i

/-- The mass of `q` remaining after removing its pointwise common mass with `p`. -/
def rightResidual (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) : ℝ :=
    q.prob i - commonMass p q i

/-- The total left residual mass after subtracting the common part of `p` and `q`. -/
def residualMass (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) : ℝ :=
    ∑ i, leftResidual p q i

/-- The pointwise common mass is nonnegative. -/
theorem commonMass_nonneg (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) : 0 ≤ commonMass p q i :=
  le_min (p.nonneg i) (q.nonneg i)

/-- The left residual mass is nonnegative at every index. -/
theorem leftResidual_nonneg (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) : 0 ≤ leftResidual p q i :=
  sub_nonneg.mpr (min_le_left _ _)

/-- The right residual mass is nonnegative at every index. -/
theorem rightResidual_nonneg (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) : 0 ≤ rightResidual p q i :=
  sub_nonneg.mpr (min_le_right _ _)

/-- The total residual mass is nonnegative. -/
theorem residualMass_nonneg (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) : 0 ≤ residualMass p q :=
  Finset.sum_nonneg fun i _ => leftResidual_nonneg p q i

/-- The total residual mass equals one minus the sum of the common masses. -/
theorem residualMass_eq_one_sub_common (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) :
    residualMass p q = 1 - ∑ i, commonMass p q i := by
  simp only [residualMass, leftResidual, Finset.sum_sub_distrib, p.sum_one]

/-- The sum of the right residual masses equals the total left residual mass. -/
theorem rightResidual_sum (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) :
    (∑ i, rightResidual p q i) = residualMass p q := by
  rw [residualMass_eq_one_sub_common]
  simp only [rightResidual, Finset.sum_sub_distrib, q.sum_one]

/-- If the total residual mass is zero, every left residual mass is zero. -/
theorem leftResidual_eq_zero_of_residualMass_eq_zero (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J)
    (h : residualMass p q = 0) (i : J) : leftResidual p q i = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => leftResidual_nonneg p q j)).mp h
    i (Finset.mem_univ i)

/-- If the total residual mass is zero, every right residual mass is zero. -/
theorem rightResidual_eq_zero_of_residualMass_eq_zero (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J)
    (h : residualMass p q = 0) (i : J) : rightResidual p q i = 0 := by
  have hs : (∑ j, rightResidual p q j) = 0 := (rightResidual_sum p q).trans h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => rightResidual_nonneg p q j)).mp hs
    i (Finset.mem_univ i)

/-- The left and right residual masses at the same index have product zero. -/
theorem residual_product_self (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) :
    leftResidual p q i * rightResidual p q i = 0 := by
  rcases le_total (p.prob i) (q.prob i) with h | h
  · simp [leftResidual, rightResidual, commonMass, min_eq_left h]
  · simp [leftResidual, rightResidual, commonMass, min_eq_right h]

/-- The absolute difference of two masses equals the sum of their left and right residual
masses. -/
theorem abs_sub_eq_residual_add (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) :
    |p.prob i - q.prob i| = leftResidual p q i + rightResidual p q i := by
  rcases le_total (p.prob i) (q.prob i) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    simp only [leftResidual, rightResidual, commonMass, min_eq_left h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    simp only [leftResidual, rightResidual, commonMass, min_eq_right h]
    ring

variable [DecidableEq J]

/-- The total residual mass equals the total variation distance `tvDist p q`. -/
theorem residualMass_eq_tvDist (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) :
    residualMass p q = Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist p q := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist
  simp_rw [abs_sub_eq_residual_add]
  rw [Finset.sum_add_distrib, rightResidual_sum]
  change residualMass p q = (1 / 2 : ℝ) * (residualMass p q + residualMass p q)
  ring

/-- The joint weight given by the common mass on the diagonal plus the product of left and right
residual masses divided by their total mass. -/
def couplingWeight (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i j : J) : ℝ :=
  (if i = j then commonMass p q i else 0) +
    leftResidual p q i * rightResidual p q j / residualMass p q

/-- Every joint weight in the common and residual coupling construction is nonnegative. -/
theorem couplingWeight_nonneg (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i j : J) :
    0 ≤ couplingWeight p q i j := by
  apply add_nonneg
  · split_ifs
    · exact commonMass_nonneg p q i
    · exact le_rfl
  · exact div_nonneg
      (mul_nonneg (leftResidual_nonneg p q i) (rightResidual_nonneg p q j))
      (residualMass_nonneg p q)

/-- The diagonal coupling weight equals the pointwise common mass. -/
theorem couplingWeight_diag (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) :
    couplingWeight p q i i = commonMass p q i := by
  simp [couplingWeight, residual_product_self]

/-- Summing coupling weights over the second coordinate recovers the mass of `p`. -/
theorem couplingWeight_row (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) :
    (∑ j, couplingWeight p q i j) = p.prob i := by
  unfold couplingWeight
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ j : J, if i = j then commonMass p q i else 0) = commonMass p q i := by
    simp
  rw [hdiag, ← Finset.sum_div, ← Finset.mul_sum, rightResidual_sum]
  by_cases hzero : residualMass p q = 0
  · rw [leftResidual_eq_zero_of_residualMass_eq_zero p q hzero i]
    have hz := leftResidual_eq_zero_of_residualMass_eq_zero p q hzero i
    simp only [leftResidual] at hz
    simp only [zero_mul, zero_div, add_zero]
    linarith
  · rw [mul_div_cancel_right₀ _ hzero]
    unfold leftResidual
    ring

/-- Summing coupling weights over the first coordinate recovers the mass of `q`. -/
theorem couplingWeight_col (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (j : J) :
    (∑ i, couplingWeight p q i j) = q.prob j := by
  unfold couplingWeight
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ i : J, if i = j then commonMass p q i else 0) = commonMass p q j := by
    simp
  rw [hdiag, ← Finset.sum_div, ← Finset.sum_mul]
  change commonMass p q j + residualMass p q * rightResidual p q j / residualMass p q = q.prob j
  by_cases hzero : residualMass p q = 0
  · rw [rightResidual_eq_zero_of_residualMass_eq_zero p q hzero j]
    have hz := rightResidual_eq_zero_of_residualMass_eq_zero p q hzero j
    simp only [rightResidual] at hz
    simp only [mul_zero, zero_div, add_zero]
    linarith
  · rw [mul_div_cancel_left₀ _ hzero]
    unfold rightResidual
    ring

/-- The finite joint distribution formed from diagonal common mass and the normalized product of
residual masses. -/
def coupling (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (J × J) where
  prob ij := couplingWeight p q ij.1 ij.2
  nonneg ij := couplingWeight_nonneg p q ij.1 ij.2
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [couplingWeight_row, p.sum_one]

/-- The mass of `(i, j)` in the constructed coupling equals `couplingWeight p q i j`. -/
@[simp] theorem coupling_apply (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i j : J) :
    (coupling p q).prob (i, j) = couplingWeight p q i j := rfl

/-- The first marginal of the constructed coupling is `p`. -/
theorem coupling_row (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (i : J) :
    (∑ j, (coupling p q).prob (i, j)) = p.prob i :=
  couplingWeight_row p q i

/-- The second marginal of the constructed coupling is `q`. -/
theorem coupling_col (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) (j : J) :
    (∑ i, (coupling p q).prob (i, j)) = q.prob j :=
  couplingWeight_col p q j

/-- The probability that the two coordinates of the constructed coupling differ equals `tvDist p
q`. -/
theorem coupling_mismatch (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist J) :
    (∑ ij : J × J, if ij.1 ≠ ij.2 then (coupling p q).prob ij else 0) =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist p q := by
  have hterm (i j : J) :
      (if i ≠ j then (coupling p q).prob (i, j) else 0) =
        leftResidual p q i * rightResidual p q j / residualMass p q := by
    by_cases hij : i = j
    · subst j
      simp [residual_product_self]
    · simp [hij, couplingWeight]
  rw [Fintype.sum_prod_type]
  simp_rw [hterm]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum, rightResidual_sum]
  rw [← Finset.sum_mul]
  change residualMass p q * residualMass p q / residualMass p q = Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist p q
  by_cases hzero : residualMass p q = 0
  · rw [hzero, zero_mul, zero_div, ← residualMass_eq_tvDist, hzero]
  · rw [mul_div_cancel_right₀ _ hzero, residualMass_eq_tvDist]

end

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteMaximalCoupling
