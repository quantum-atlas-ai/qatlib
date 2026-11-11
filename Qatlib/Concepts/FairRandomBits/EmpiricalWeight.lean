/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

/-!
# Empirical weights and preparation counts

`empiricalWeight` assigns each optional finite label its sample count as a rational weight. The
module computes its total mass and the comparison and adjoint-gate counts of the associated
`empiricalPrepare` construction.

The recursive counter `empiricalNativeCounts` returns all label counts together with exact
sample and comparison totals. The preparation of amplitudes from classical distribution data is
discussed in [GroverRudolph2002].

## Main statements

* `empirical_native_weights_and_work`: empirical weights have mass `N` and the stated
  preparation resource counts.
* `empiricalNativeCounts_correct`: the native counter computes label multiplicities and exact
  work totals.

## References

* [Grover and Rudolph, 2002][GroverRudolph2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The unnormalized empirical weight of a label, given by its multiplicity in the sample list
as a rational number. -/
def empiricalWeight {n N : ℕ} (ω : Fin N→Option (Fin n)) (a : Option (Fin n)) : ℚ :=
  ((List.ofFn ω).count a:ℚ)

/-- The rational-weight preparation associated with the empirical label counts and the chosen
bit precision. -/
noncomputable def empiricalPrepare {n N : ℕ} (ω : Fin N→Option (Fin n)) (bits : ℕ) :=
  rationalWeightPrepare (empiricalWeight ω) bits

/-- Every empirical label weight is nonnegative. -/
theorem empiricalWeight_nonneg {n N : ℕ} (ω : Fin N → Option (Fin n))
    (a : Option (Fin n)) : 0 ≤ empiricalWeight ω a := by
  unfold empiricalWeight
  positivity

/-- Summing a function against label multiplicities equals summing it over the original list. -/
theorem empirical_count_sum {α : Type} [Fintype α] [BEq α] [LawfulBEq α]
    (xs : List α) (f : α → ℚ) :
    (∑ a, (xs.count a : ℚ) * f a) = (xs.map f).sum := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, Nat.cast_add, beq_iff_eq, List.map_cons, List.sum_cons]
    have he : ∀ a, (((if x=a then 1 else 0 : ℕ) : ℚ) * f a) =
        if a=x then f x else 0 := by
      intro a
      by_cases h : a=x
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [add_mul, he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ih, add_comm]

/-- Empirical weights are nonnegative with total mass `N`; their preparation uses `2 * n * bits`
comparisons and `n` adjoint gates. -/
theorem empirical_native_weights_and_work : ∀ (n N bits : ℕ) (ω : Fin N → Option (Fin n)),
    (∀ a, 0 ≤ empiricalWeight ω a) ∧ rationalWeightMass (empiricalWeight ω) = (N : ℚ) ∧
    rationalWeightComparisons (empiricalWeight ω) bits = 2*n*bits ∧
    adjointGateCount (rationalWeightWord (empiricalWeight ω) bits) = n := by
  intro n N bits ω
  refine ⟨empiricalWeight_nonneg ω, ?_,
    (rational_weight_data_ranges_and_actual_comparisons n bits _ (empiricalWeight_nonneg ω)).2.2,
    (weight_fixed_word_counts (fun j => rationalWeightGate (empiricalWeight ω) bits j)).2⟩
  have h := empirical_count_sum (List.ofFn ω) (fun _ => 1)
  simpa [rationalWeightMass, empiricalWeight, List.map_const', Function.comp_def,
      List.ofFn_const] using h

/-- Count every optional label while recording the number of samples processed and the number of
label comparisons. -/
def empiricalNativeCounts {n : ℕ} : List (Option (Fin n)) →
    List (Option (Fin n) × ℕ) × ℕ × ℕ
  | [] => ((none :: List.ofFn (fun i : Fin n => some i)).map (fun a => (a,0)), 0, 0)
  | a :: xs =>
    let z := empiricalNativeCounts xs
    (z.1.map (fun b => (b.1, b.2 + if a=b.1 then 1 else 0)), z.2.1+1, z.2.2+z.1.length)

/-- The native counter returns all label multiplicities, the list length, and exactly `(n + 1) *
xs.length` comparisons. -/
theorem empiricalNativeCounts_correct {n : ℕ} (xs : List (Option (Fin n))) :
    (empiricalNativeCounts xs).1 =
      (none :: List.ofFn (fun i : Fin n => some i)).map (fun a => (a,xs.count a)) ∧
      (empiricalNativeCounts xs).2.1 = xs.length ∧
      (empiricalNativeCounts xs).2.2 = (n+1)*xs.length := by
  induction xs with
  | nil => simp [empiricalNativeCounts]
  | cons a xs ih =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [empiricalNativeCounts, ih.1, List.map_map, Function.comp_def,
        List.count_cons, beq_iff_eq]
    · simp [empiricalNativeCounts, ih.2.1]
    · simp [empiricalNativeCounts, ih.1, ih.2.2, Nat.mul_add, Nat.mul_one, add_comm]

/-- On `List.ofFn ω`, the native counts reproduce the empirical rational weights and record `N`
samples and `(n + 1) * N` comparisons. -/
theorem empiricalNativeCounts_weight {n N : ℕ} (ω : Fin N → Option (Fin n)) :
    (empiricalNativeCounts (List.ofFn ω)).1.map (fun z => (z.1,(z.2 : ℚ))) =
      (none :: List.ofFn (fun i : Fin n => some i)).map (fun a => (a,empiricalWeight ω a)) ∧
      (empiricalNativeCounts (List.ofFn ω)).2.1 = N ∧
      (empiricalNativeCounts (List.ofFn ω)).2.2 = (n+1)*N := by
  refine ⟨?_, ?_⟩
  · simp only [(empiricalNativeCounts_correct (List.ofFn ω)).1, List.map_map,
      Function.comp_def, empiricalWeight]
  · simpa only [List.length_ofFn] using (empiricalNativeCounts_correct (List.ofFn ω)).2

end Qatlib.Concepts.FairRandomBits.EmpiricalWeight
