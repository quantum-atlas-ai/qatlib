/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashPartitionData
import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashVector
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

/-!
# Weighted hash deviation with side information

The module realizes each side information class as a masked complex weight and applies the
vector hash estimate to these masks. It bounds the average sum of absolute bucket deviations by
a square root involving the side information cardinality, bucket cardinality, and total squared
input weight.

This finite aggregation estimate complements the sampling and sketching framework of
[ChiaEtAl2022].

## Main statements

* `partition_masked_vector_mass`: masking partitions the squared input mass.
* `weighted_hash_partition_deviation_bound`: the average partition deviation estimate.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

open scoped BigOperators

/-- A joint hash and side information bucket is a hash bucket of the weight masked to that side
information value. -/
private theorem partition_bucket_masked
    {H X A T : Type} [Fintype X] [DecidableEq A] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ)
    (r : H) (a : A) (t : T) :
    weightedHashPartitionBucket hash side p r a t =
      weightedHashBucket hash (weightedHashPartitionWeight side p t) r a := by
  unfold weightedHashPartitionBucket weightedHashBucket
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : hash r x = a <;> simp [weightedHashPartitionWeight, hx]

/-- A centered joint bucket equals the hash deviation of the weight masked to its side
information value. -/
private theorem partition_deviation_masked
    {H X A T : Type} [Fintype X] [Fintype A] [DecidableEq A] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ)
    (r : H) (a : A) (t : T) :
    weightedHashPartitionBucket hash side p r a t -
        (Fintype.card A : ℂ)⁻¹ * weightedHashSideMass side p t =
      weightedHashDeviation hash (weightedHashPartitionWeight side p t) r a := by
  rw [partition_bucket_masked]
  rfl

/-- The total vector mass of all side information masks equals the total squared norm of the
original weights. -/
private theorem partition_masked_vector_mass
    {X T : Type} [Fintype X] [Fintype T] [DecidableEq T]
    (side : X → T) (p : X → ℂ) :
    weightedHashVectorMass (weightedHashPartitionWeight side p) =
      ∑ x : X, Complex.normSq (p x) := by
  unfold weightedHashVectorMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hterm (t : T) :
      Complex.normSq (weightedHashPartitionWeight side p t x) =
        if side x = t then Complex.normSq (p x) else 0 := by
    by_cases ht : side x = t <;> simp [weightedHashPartitionWeight, ht]
  simp_rw [hterm]
  simp

/-- Under reciprocal cardinality pair collision probabilities, the average partition deviation
is at most `sqrt (|T| * (|A| - 1) * ∑ x, Complex.normSq (p x))`. -/
theorem weighted_hash_partition_deviation_bound
    (H X A T : Type) [Fintype H] [Nonempty H] [Fintype X]
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype T] [DecidableEq T]
    (hash : H → X → A) (side : X → T) (p : X → ℂ)
    (hcollision : ∀ x y : X, x ≠ y →
      finiteHashAverage (fun r : H => if hash r x = hash r y then 1 else 0) =
        (Fintype.card A : ℝ)⁻¹) :
    finiteHashAverage (weightedHashPartitionDeviation hash side p) ≤
      Real.sqrt ((Fintype.card T : ℝ) * ((Fintype.card A : ℝ) - 1) *
        ∑ x : X, Complex.normSq (p x)) := by
  let f : T → X → ℂ := weightedHashPartitionWeight side p
  have hTnonneg : 0 ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  have hlabel (r : H) (a : A) :
      (∑ t : T, ‖weightedHashDeviation hash (f t) r a‖) ≤
        Real.sqrt (Fintype.card T : ℝ) *
          Real.sqrt (∑ t : T, Complex.normSq (weightedHashDeviation hash (f t) r a)) := by
    have hcs : (∑ t : T, ‖weightedHashDeviation hash (f t) r a‖) ^ 2 ≤
        (Fintype.card T : ℝ) *
          ∑ t : T, Complex.normSq (weightedHashDeviation hash (f t) r a) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset T)
        (fun _ : T => (1 : ℝ))
        (fun t : T => ‖weightedHashDeviation hash (f t) r a‖)
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Complex.sq_norm] using h
    simpa only [Real.sqrt_mul hTnonneg] using Real.le_sqrt_of_sq_le hcs
  have hpoint (r : H) :
      weightedHashPartitionDeviation hash side p r ≤
        Real.sqrt (Fintype.card T : ℝ) * weightedHashVectorDeviation hash f r := by
    unfold weightedHashPartitionDeviation
    simp_rw [partition_deviation_masked]
    calc
      _ ≤ ∑ a : A, Real.sqrt (Fintype.card T : ℝ) *
          Real.sqrt (∑ t : T, Complex.normSq (weightedHashDeviation hash (f t) r a)) :=
        Finset.sum_le_sum (fun a _ => hlabel r a)
      _ = _ := by
        rw [← Finset.mul_sum]
        rfl
  have havg : finiteHashAverage (weightedHashPartitionDeviation hash side p) ≤
      Real.sqrt (Fintype.card T : ℝ) *
        finiteHashAverage (weightedHashVectorDeviation hash f) := by
    unfold finiteHashAverage
    calc
      _ ≤ (Fintype.card H : ℝ)⁻¹ *
          ∑ r : H, Real.sqrt (Fintype.card T : ℝ) *
            weightedHashVectorDeviation hash f r :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun r _ => hpoint r))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = _ := by
        rw [← Finset.mul_sum]
        ring
  have hmass : weightedHashVectorMass f = ∑ x : X, Complex.normSq (p x) :=
    partition_masked_vector_mass side p
  have hvector := weighted_hash_vector_deviation_bound H X A T hash f hcollision
  rw [hmass] at hvector
  calc
    _ ≤ Real.sqrt (Fintype.card T : ℝ) *
        finiteHashAverage (weightedHashVectorDeviation hash f) := havg
    _ ≤ Real.sqrt (Fintype.card T : ℝ) *
        Real.sqrt (((Fintype.card A : ℝ) - 1) *
          ∑ x : X, Complex.normSq (p x)) :=
      mul_le_mul_of_nonneg_left hvector (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.sqrt_mul hTnonneg]
      congr 1
      ring

end Qatlib.Concepts.ProbabilityCore.Concentration
