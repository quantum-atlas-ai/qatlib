/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceMarkSetHybrid
import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Tactic.Linarith

/-!
# Single-address oracle changes and exceptional sets

This module proves a finite Boolean XOR-oracle version of the exceptional-set estimate
associated with Corollary 3.4 of [BennettEtAl1997]. `accumulatedQueryMass` sums the probability
of querying one address along the reference-oracle execution; for a unitary circuit and a
normalized initial state, these masses sum to the query count.

The estimate uses the explicit constant four for this oracle primitive and query-count
convention. If each oracle `Ay y` agrees with the reference away from `y`, all but at most `4 *
T^2 / ε^2` addresses produce final states at Euclidean distance at most `ε`, where `T` is the
positive number of queries.

## Main statements

* `sum_accumulatedQueryMass` gives the total query-mass identity.
* `single_address_final_distance_sq` bounds the squared final distance by `4 * T` times the
  address's accumulated mass.
* `total_single_address_distance_sq_le` bounds the sum of squared distances by `4 * T^2`.
* `corollary3_4_bad_set` constructs the exceptional set for positive `ε`.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Matrix
open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators

section Generic

/-- Interchange a finite sum over indices with the sum of a real-valued function over a list. -/
private theorem sum_list_map_comm {α I : Type} [Fintype I] (L : List α) (g : α → I → ℝ) :
    (∑ i : I, (L.map (fun a => g a i)).sum) = (L.map (fun a => ∑ i : I, g a i)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih]

/-- Pointwise inequalities on the elements of a list imply the corresponding inequality between
the sums of the mapped real-valued functions. -/
private theorem list_map_sum_le {α : Type*} (L : List α) {f g : α → ℝ}
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- If nonnegative masses sum to a positive value `T`, at most `4 * T^2 / ε^2` indices have mass
at least `ε^2 / (4 * T)` for positive `ε`. -/
theorem card_threshold_set_le {I : Type} [Fintype I] (q : I → ℝ) (hq : ∀ y : I, 0 ≤ q y)
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) (hsum : ∑ y : I, q y = T) :
    ((Finset.univ.filter fun y : I => ε ^ 2 / (4 * T) ≤ q y).card : ℝ) ≤ 4 * T ^ 2 / ε ^ 2 := by
  have hc : (0 : ℝ) < ε ^ 2 / (4 * T) := by positivity
  have hbound : ((Finset.univ.filter fun y : I => ε ^ 2 / (4 * T) ≤ q y).card : ℝ) *
      (ε ^ 2 / (4 * T)) ≤ T := by
    calc ((Finset.univ.filter fun y : I => ε ^ 2 / (4 * T) ≤ q y).card : ℝ) *
          (ε ^ 2 / (4 * T))
        = ∑ _y ∈ Finset.univ.filter (fun y : I => ε ^ 2 / (4 * T) ≤ q y),
            ε ^ 2 / (4 * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ Finset.univ.filter (fun y : I => ε ^ 2 / (4 * T) ≤ q y), q y :=
          Finset.sum_le_sum fun y hy => (Finset.mem_filter.mp hy).2
      _ ≤ ∑ y : I, q y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => hq i)
      _ = T := hsum
  have hdiv := (le_div_iff₀ hc).mpr hbound
  have heq : T / (ε ^ 2 / (4 * T)) = 4 * T ^ 2 / ε ^ 2 := by
    field_simp
  rwa [heq] at hdiv

end Generic

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- Sum the probability mass of the query-address fiber at `y` over all states immediately
before oracle queries in the execution with reference oracle `A`. -/
noncomputable def accumulatedQueryMass (A : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (y : I) : ℝ :=
  ((oracleQueryInputs A C ψ).map (fun φ => MeasureProb φ (workspaceQueryFiber (W := W) y))).sum

/-- The accumulated query mass at each address is nonnegative because it is a sum of measurement
probabilities. -/
theorem accumulatedQueryMass_nonneg (A : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (y : I) : 0 ≤ accumulatedQueryMass A C ψ y := by
  unfold accumulatedQueryMass
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hx
  exact measureProb_nonneg φ _

/-- For a unitary circuit and a normalized initial state, the accumulated masses over all query
addresses sum to the number of oracle queries. This is the query-mass accounting used in the
finite-oracle version of Corollary 3.4 of [BennettEtAl1997]. -/
theorem sum_accumulatedQueryMass (A : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    ∑ y : I, accumulatedQueryMass A C ψ y = (QueryCount C : ℝ) := by
  obtain ⟨hlen, hmem⟩ := oracle_query_inputs_accounting A C ψ hC hψ
  have hcomm := sum_list_map_comm (oracleQueryInputs A C ψ)
    (fun φ (y : I) => MeasureProb φ (workspaceQueryFiber (W := W) y))
  have hstep : (oracleQueryInputs A C ψ).map
      (fun φ => ∑ y : I, MeasureProb φ (workspaceQueryFiber (W := W) y))
      = (oracleQueryInputs A C ψ).map (fun _ => (1 : ℝ)) :=
    List.map_congr_left fun φ hφ => (hmem φ hφ).2
  calc ∑ y : I, accumulatedQueryMass A C ψ y
      = ∑ y : I, ((oracleQueryInputs A C ψ).map
          (fun φ => MeasureProb φ (workspaceQueryFiber (W := W) y))).sum := rfl
    _ = ((oracleQueryInputs A C ψ).map
          (fun φ => ∑ y : I, MeasureProb φ (workspaceQueryFiber (W := W) y))).sum := hcomm
    _ = ((oracleQueryInputs A C ψ).map (fun _ => (1 : ℝ))).sum := by rw [hstep]
    _ = ((oracleQueryInputs A C ψ).length : ℝ) := by
        induction oracleQueryInputs A C ψ with
        | nil => simp
        | cons a t ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [ih]; push_cast; ring
    _ = (QueryCount C : ℝ) := by rw [hlen]

/-- If `B` agrees with `A` away from one address `y`, their final states from a normalized seed
in a unitary circuit have squared Euclidean distance at most `4 * QueryCount C *
accumulatedQueryMass A C ψ y`. -/
theorem single_address_final_distance_sq (A B : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (y : I)
    (hagree : ∀ x : I, x ≠ y → B x = A x) :
    ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) B) C ψ -
        Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2
      ≤ 4 * (QueryCount C : ℝ) * accumulatedQueryMass A C ψ y := by
  have hsub : workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => A x ≠ B x))
      ⊆ workspaceQueryFiber (W := W) y := by
    intro p hp
    have hp1 : p.1.1 ∈ Finset.univ.filter (fun x : I => A x ≠ B x) := by
      simpa [workspaceMarkFiber] using hp
    have hne : A p.1.1 ≠ B p.1.1 := (Finset.mem_filter.mp hp1).2
    have hpy : p.1.1 = y := by
      by_contra hne'
      exact hne (by rw [hagree p.1.1 hne'])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpy⟩
  have hle : ((oracleQueryInputs A C ψ).map (fun φ => MeasureProb φ
        (workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => A x ≠ B x))))).sum
      ≤ accumulatedQueryMass A C ψ y :=
    list_map_sum_le _ fun φ _ =>
      Qatlib.Foundations.BornMetrics.EventProbability.measureProb_mono φ hsub
  have hE := workspace_mark_set_hybrid_energy (W := W) A B C ψ hC hψ
  calc ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) B) C ψ -
        Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2
      ≤ 4 * (QueryCount C : ℝ) * ((oracleQueryInputs A C ψ).map (fun φ => MeasureProb φ
          (workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => A x ≠ B x))))).sum := hE
    _ ≤ 4 * (QueryCount C : ℝ) * accumulatedQueryMass A C ψ y :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- For a family of oracles differing from the reference only at their indexed addresses, the
sum of squared final-state distances is at most four times the square of the circuit's query
count. The circuit is assumed unitary and its initial state normalized. -/
theorem total_single_address_distance_sq_le (A : I → Bool) (Ay : I → I → Bool)
    (hAy : ∀ (y : I) (x : I), x ≠ y → Ay y x = A x)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    ∑ y : I, ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
        Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2
      ≤ 4 * (QueryCount C : ℝ) ^ 2 := by
  have hsum := sum_accumulatedQueryMass A C ψ hC hψ
  have hstep : ∑ y : I, ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
      Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2
      ≤ ∑ y : I, 4 * (QueryCount C : ℝ) * accumulatedQueryMass A C ψ y :=
    Finset.sum_le_sum fun y _ => single_address_final_distance_sq A (Ay y) C ψ hC hψ y (hAy y)
  calc ∑ y : I, ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
        Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2
      ≤ ∑ y : I, 4 * (QueryCount C : ℝ) * accumulatedQueryMass A C ψ y := hstep
    _ = 4 * (QueryCount C : ℝ) * ∑ y : I, accumulatedQueryMass A C ψ y := by
        rw [Finset.mul_sum]
    _ = 4 * (QueryCount C : ℝ) ^ 2 := by rw [hsum]; ring

/-- For a unitary circuit with a normalized seed, positive query count `T`, and positive
tolerance `ε`, there is an exceptional set of at most `4 * T^2 / ε^2` addresses outside
which every permitted single-address oracle change alters the final state by Euclidean
distance at most `ε`. This is the finite Boolean XOR-oracle estimate associated with
Corollary 3.4 of [BennettEtAl1997], with its explicit constant four. -/
theorem corollary3_4_bad_set (A : I → Bool) (Ay : I → I → Bool)
    (hAy : ∀ (y : I) (x : I), x ≠ y → Ay y x = A x)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (hT : 0 < QueryCount C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, (S.card : ℝ) ≤ 4 * (QueryCount C : ℝ) ^ 2 / ε ^ 2 ∧
      ∀ y : I, y ∉ S →
        ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
            Run (workspaceBitOracle (W := W) A) C ψ)‖ ≤ ε := by
  refine ⟨Finset.univ.filter (fun y : I => ε ^ 2 / (4 * (QueryCount C : ℝ)) ≤
      accumulatedQueryMass A C ψ y), ?_, ?_⟩
  · exact card_threshold_set_le (fun y => accumulatedQueryMass A C ψ y)
      (fun y => accumulatedQueryMass_nonneg A C ψ y) _ ε (by exact_mod_cast hT) hε
      (sum_accumulatedQueryMass A C ψ hC hψ)
  · intro y hy
    have hq : accumulatedQueryMass A C ψ y < ε ^ 2 / (4 * (QueryCount C : ℝ)) := by
      by_contra hle
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hle⟩)
    have hT' : (0 : ℝ) < (QueryCount C : ℝ) := by exact_mod_cast hT
    have hd := single_address_final_distance_sq A (Ay y) C ψ hC hψ y (hAy y)
    have hpos : (0 : ℝ) < 4 * (QueryCount C : ℝ) := by positivity
    have hd2 : ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
        Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2 < ε ^ 2 := by
      calc ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
            Run (workspaceBitOracle (W := W) A) C ψ)‖ ^ 2
          ≤ 4 * (QueryCount C : ℝ) * accumulatedQueryMass A C ψ y := hd
        _ < 4 * (QueryCount C : ℝ) * (ε ^ 2 / (4 * (QueryCount C : ℝ))) :=
            mul_lt_mul_of_pos_left hq hpos
        _ = ε ^ 2 := by field_simp
    have hnn : (0 : ℝ) ≤ ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
        Run (workspaceBitOracle (W := W) A) C ψ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (Ay y)) C ψ -
      Run (workspaceBitOracle (W := W) A) C ψ)‖ - ε)]

end Qatlib.Papers.QWeakness97.MainResults
