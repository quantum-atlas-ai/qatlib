/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FermionicSim00.MainResults.StatePreparation
public import Qatlib.Papers.FermionicSim00.MainResults.MeasurementStatistics

@[expose] public section

/-!
# Finite preparation and measurement bounds

In [Ortiz et al.][OrtizEtAl2001], §IV.B bounds the initial-state construction
cost using the electron count. Section IV.D.3 reduces measurement noise by
repetition. These bounds use the respective preparation cost expression and
bounded random variables on a probability space with the stated independence.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Qatlib.Papers.FermionicSim00.MainResults

namespace Qatlib.Papers.FermionicSim00.MainResults

/-- The source bound `Ne ≤ n` gives a polynomial preparation budget with
unit constant when the number of determinants is at most `n ^ k`. -/
theorem construction_cost_polynomial_of_le (N n Ne k : ℕ)
    (hN : N ≤ n ^ k) (hNe : Ne ≤ n) :
    N ^ 2 * n * Ne ≤ n ^ (2 * k + 2) := by
  calc
    N ^ 2 * n * Ne ≤ N ^ 2 * n ^ 2 := construction_cost_le_of_le N n Ne hNe
    _ ≤ (n ^ k) ^ 2 * n ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 2)
    _ = n ^ (2 * k + 2) := by rw [← pow_mul, mul_comm k 2, pow_add]

/-- The variance of a sum of bounded pairwise independent measurements is
at most the number of terms times a common bound on each term's variance. -/
theorem variance_sum_le_of_variance_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (B : ℝ) (X : Fin m → Ω → ℝ)
    (hX : ∀ j, AEMeasurable (X j) μ)
    (hb : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : ∀ i j : Fin m, i ≠ j → IndepFun (X i) (X j) μ)
    (hvar : ∀ j, variance (X j) μ ≤ B) :
    variance (fun ω => ∑ j, X j ω) μ ≤ (m : ℝ) * B := by
  have hsum : variance (fun ω => ∑ j, X j ω) μ = ∑ j, variance (X j) μ := by
    have hlp (j : Fin m) : MemLp (X j) 2 μ :=
      memLp_of_bounded (hb j) (hX j).aestronglyMeasurable 2
    have h := IndepFun.variance_sum (s := Finset.univ)
      (fun i _ => hlp i) (fun i _ j _ hij => hindep i j hij)
    convert h using 2
    ext ω
    simp [Finset.sum_apply]
  calc
    _ = ∑ j, variance (X j) μ := hsum
    _ ≤ ∑ _j : Fin m, B := Finset.sum_le_sum fun j _ => hvar j
    _ = (m : ℝ) * B := by simp

/-- Averaging `K` pairwise independent repetitions of a measurement with
outcomes in `[-1, 1]` gives variance at most `1 / K`. -/
theorem repeated_measurement_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} (hK : 0 < K)
    (X : Fin K → Ω → ℝ) (hX : ∀ j, AEMeasurable (X j) μ)
    (hb : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : ∀ i j : Fin K, i ≠ j → IndepFun (X i) (X j) μ) :
    variance (fun ω => (K : ℝ)⁻¹ * ∑ j, X j ω) μ ≤ 1 / (K : ℝ) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  calc
    _ = ((K : ℝ)⁻¹) ^ 2 * variance (fun ω => ∑ j, X j ω) μ :=
      variance_const_mul _ _ _
    _ ≤ ((K : ℝ)⁻¹) ^ 2 * (K : ℝ) :=
      mul_le_mul_of_nonneg_left (variance_sum_le_card X hX hb hindep) (sq_nonneg _)
    _ = 1 / (K : ℝ) := by field_simp

end Qatlib.Papers.FermionicSim00.MainResults
