/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashVectorData
import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashMoment
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SimpRw

/-!
# Average vector hash deviation bounds

The module combines finite averaging, a sum of squares inequality, and the scalar hash second
moment identity to control vector bucket deviations. Reciprocal cardinality collision
probabilities give a square root bound in terms of the total squared component mass.

The argument supplies finite weighted aggregation estimates for sampling and sketching contexts
such as [ChiaEtAl2022].

## Main statements

* `vector_hash_average_sum_square_le`: a finite averaging and sum of squares estimate.
* `weighted_hash_vector_deviation_bound`: average vector deviation bounded by `sqrt ((|A| - 1) *
  weightedHashVectorMass f)`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped BigOperators

/-- Finite hash averaging commutes with summation over vector components. -/
private theorem vector_hash_average_sum
    {H T : Type} [Fintype H] [Fintype T] (g : H → T → ℝ) :
    finiteHashAverage (fun r : H => ∑ k : T, g r k) =
      ∑ k : T, finiteHashAverage (fun r : H => g r k) := by
  unfold finiteHashAverage
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The square of the average sum over `A` is at most `|A|` times the average sum of squares,
for a nonempty seed type. -/
private theorem vector_hash_average_sum_square_le
    {H A : Type} [Fintype H] [Nonempty H] [Fintype A]
    (g : H → A → ℝ) :
    (finiteHashAverage (fun r : H => ∑ a : A, g r a)) ^ 2 ≤
      (Fintype.card A : ℝ) *
        finiteHashAverage (fun r : H => ∑ a : A, (g r a) ^ 2) := by
  classical
  have hn : (Fintype.card H : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcs : (∑ r : H, ∑ a : A, g r a) ^ 2 ≤
      (Fintype.card H : ℝ) * (Fintype.card A : ℝ) *
        (∑ r : H, ∑ a : A, (g r a) ^ 2) := by
    have hp := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (H × A))
      (fun _ : H × A => (1 : ℝ)) (fun ra : H × A => g ra.1 ra.2)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Fintype.card_prod, Nat.cast_mul,
      Fintype.sum_prod_type] using hp
  unfold finiteHashAverage
  calc
    ((Fintype.card H : ℝ)⁻¹ * (∑ r : H, ∑ a : A, g r a)) ^ 2 =
        ((Fintype.card H : ℝ)⁻¹) ^ 2 *
          (∑ r : H, ∑ a : A, g r a) ^ 2 := by ring
    _ ≤ ((Fintype.card H : ℝ)⁻¹) ^ 2 *
        ((Fintype.card H : ℝ) * (Fintype.card A : ℝ) *
          (∑ r : H, ∑ a : A, (g r a) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = (Fintype.card A : ℝ) *
        ((Fintype.card H : ℝ)⁻¹ *
          (∑ r : H, ∑ a : A, (g r a) ^ 2)) := by
      field_simp [hn]

/-- Under reciprocal cardinality pair collision probabilities, the average vector hash deviation
is at most `sqrt ((|A| - 1) * weightedHashVectorMass f)`. -/
theorem weighted_hash_vector_deviation_bound
    (H X A T : Type) [Fintype H] [Nonempty H] [Fintype X]
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype T]
    (hash : H → X → A) (f : T → X → ℂ)
    (hcollision : ∀ x y : X, x ≠ y →
      finiteHashAverage (fun r : H => if hash r x = hash r y then 1 else 0) =
        (Fintype.card A : ℝ)⁻¹) :
    finiteHashAverage (weightedHashVectorDeviation hash f) ≤
      Real.sqrt (((Fintype.card A : ℝ) - 1) * weightedHashVectorMass f) := by
  classical
  have hn : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmoment (k : T) :
      finiteHashAverage (fun r : H => ∑ a : A,
        Complex.normSq (weightedHashDeviation hash (f k) r a)) =
        (1 - (Fintype.card A : ℝ)⁻¹) *
          ∑ x : X, Complex.normSq (f k x) := by
    simpa only [weightedHashDeviation] using
      weighted_hash_centered_second_moment H X A hash (f k) hcollision
  have henergy : finiteHashAverage (fun r : H => ∑ a : A, ∑ k : T,
      Complex.normSq (weightedHashDeviation hash (f k) r a)) =
      (1 - (Fintype.card A : ℝ)⁻¹) * weightedHashVectorMass f := by
    calc
      _ = finiteHashAverage (fun r : H => ∑ k : T, ∑ a : A,
          Complex.normSq (weightedHashDeviation hash (f k) r a)) := by
        congr 1
        funext r
        rw [Finset.sum_comm]
      _ = ∑ k : T, finiteHashAverage (fun r : H => ∑ a : A,
          Complex.normSq (weightedHashDeviation hash (f k) r a)) :=
        vector_hash_average_sum _
      _ = (1 - (Fintype.card A : ℝ)⁻¹) * weightedHashVectorMass f := by
        simp_rw [hmoment]
        rw [← Finset.mul_sum]
        rfl
  have hsqrt (r : H) (a : A) :
      (Real.sqrt (∑ k : T, Complex.normSq
        (weightedHashDeviation hash (f k) r a))) ^ 2 =
      ∑ k : T, Complex.normSq (weightedHashDeviation hash (f k) r a) :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  have hcs := vector_hash_average_sum_square_le
    (fun (r : H) (a : A) => Real.sqrt (∑ k : T,
      Complex.normSq (weightedHashDeviation hash (f k) r a)))
  change (finiteHashAverage (weightedHashVectorDeviation hash f)) ^ 2 ≤
    (Fintype.card A : ℝ) * finiteHashAverage (fun r : H => ∑ a : A,
      (Real.sqrt (∑ k : T, Complex.normSq
        (weightedHashDeviation hash (f k) r a))) ^ 2) at hcs
  simp_rw [hsqrt] at hcs
  rw [henergy] at hcs
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ (Fintype.card A : ℝ) *
        ((1 - (Fintype.card A : ℝ)⁻¹) * weightedHashVectorMass f) := hcs
    _ = ((Fintype.card A : ℝ) - 1) * weightedHashVectorMass f := by
      have hcancel : (Fintype.card A : ℝ) * (Fintype.card A : ℝ)⁻¹ = 1 :=
        mul_inv_cancel₀ hn
      calc
        _ = ((Fintype.card A : ℝ) -
            (Fintype.card A : ℝ) * (Fintype.card A : ℝ)⁻¹) *
            weightedHashVectorMass f := by ring
        _ = _ := by rw [hcancel]

end Qatlib.Concepts.ProbabilityCore.Concentration
