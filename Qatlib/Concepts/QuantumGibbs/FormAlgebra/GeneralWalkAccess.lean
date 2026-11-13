/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# General kernel row-state preparation

This module realizes ideal and computed preparation of a rational transition row after moving a
chosen pivot to the distinguished vertex. It proves evaluation identities, operator and state
error bounds, and exact gate and comparison counts, furnishing row-state setup ingredients for
quantum walks such as [Szegedy2004].

## Main statements

* `generalIdealSetupWord_exact`: Ideal setup prepares the exact square-root transition row.
* `generalSetupWord_matrix_error`: An explicit operator-norm approximation bound.
* `clause37_complete`: The combined row-setup realization and cost account.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
namespace GeneralWalkAccess

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- For a word consisting of fixed gates, relabeling and then reversing commutes with evaluation
up to relabeling the evaluated matrix. -/
theorem evaluate_relabel_reverse {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (cs : List (AdjointStep I))
    (hg : ∀ c ∈ cs, ∃ V, c = AdjointStep.gate V) :
    evaluate (1 : Matrix J J ℂ) ((cs.map (relabelAdjointStep e)).reverse)
      = relabelGate e (evaluate (1 : Matrix I I ℂ) cs.reverse) := by
  induction cs with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, evaluate]
    rw [CircuitRelabel.relabelGate_one e]
  | cons c cs ih =>
    obtain ⟨V, rfl⟩ := hg c (by simp)
    have hgs : ∀ c' ∈ cs, ∃ V', c' = AdjointStep.gate V' := by
      intro c' hc'
      exact hg c' (by simp [hc'])
    have hmap : List.map (relabelAdjointStep e) (AdjointStep.gate V :: cs)
        = (relabelAdjointStep e (AdjointStep.gate V))
            :: List.map (relabelAdjointStep e) cs := by
      simp
    rw [hmap, List.reverse_cons, List.reverse_cons]
    rw [evaluate_append, evaluate_append]
    rw [ih hgs]
    simp only [relabelAdjointStep_gate, evaluate, instructionMatrix, Matrix.mul_one]
    rw [CircuitRelabel.relabelGate_mul e]

/-- The computed setup word is the reversed list of pivot-relabelled rational weight gates. -/
theorem generalSetupWord_eq {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) (k : ℕ) :
    generalSetupWord K p k
      = (List.ofFn (fun j => AdjointStep.gate
          (relabelGate (pivotRelabel p) (rationalWeightGate (rowWeight K p) k j)))).reverse := by
  unfold generalSetupWord
  rw [rationalWeightWord, List.map_reverse, List.map_ofFn]
  rfl

/-- The ideal setup word is the reversed list of pivot-relabelled ideal weight gates. -/
theorem generalIdealSetupWord_eq {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    generalIdealSetupWord K p
      = (List.ofFn (fun j => AdjointStep.gate
          (relabelGate (pivotRelabel p) (idealWeightGate (rowWeight K p) j)))).reverse := by
  unfold generalIdealSetupWord
  rw [idealWeightWord, List.map_reverse, List.map_ofFn]
  rfl

/-- The computed kernel row-setup word is a well-formed adjoint circuit. -/
theorem generalSetupWord_wellFormed {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (k : ℕ) : WellFormedAdjointCircuit (generalSetupWord K p k) := by
  intro W hW
  have hWmem : AdjointStep.gate W ∈ List.ofFn (fun j : Fin V => AdjointStep.gate
      (relabelGate (pivotRelabel p) (rationalWeightGate (rowWeight K p) k j))) := by
    have heq := generalSetupWord_eq K p k
    rw [heq, List.mem_reverse] at hW
    exact hW
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hWmem
  have hWgate : W = relabelGate (pivotRelabel p) (rationalWeightGate (rowWeight K p) k j) :=
    (AdjointStep.gate.inj hj).symm
  rw [hWgate]
  exact (relabelGate_mem_unitaryGroup (pivotRelabel p)
    (rationalWeightGate (rowWeight K p) k j)).mpr (rationalWeightGate_unitary (rowWeight K p) k j)

/-- The computed setup word evaluates to the pivot relabeling of the rational weight preparation
matrix. -/
theorem generalSetupWord_evaluate {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) (k : ℕ) :
    evaluate 1 (generalSetupWord K p k)
      = relabelGate (pivotRelabel p) (rationalWeightPrepare (rowWeight K p) k) := by
  unfold generalSetupWord
  rw [rationalWeightWord, List.map_reverse]
  have hg : ∀ c ∈ (List.ofFn (fun j : Fin V => AdjointStep.gate
      (rationalWeightGate (rowWeight K p) k j))), ∃ V, c = AdjointStep.gate V := by
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hc
    exact ⟨rationalWeightGate (rowWeight K p) k j, hj ▸ rfl⟩
  have h := evaluate_relabel_reverse (pivotRelabel p)
    (List.ofFn (fun j : Fin V => AdjointStep.gate (rationalWeightGate (rowWeight K p) k j))) hg
  rw [h]
  rfl

/-- The ideal setup word evaluates to the pivot relabeling of the ideal weight preparation
matrix. -/
theorem generalIdealSetupWord_evaluate {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    evaluate 1 (generalIdealSetupWord K p)
      = relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)) := by
  unfold generalIdealSetupWord
  rw [idealWeightWord, List.map_reverse]
  have hg : ∀ c ∈ (List.ofFn (fun j : Fin V => AdjointStep.gate
      (idealWeightGate (rowWeight K p) j))), ∃ V, c = AdjointStep.gate V := by
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hc
    exact ⟨idealWeightGate (rowWeight K p) j, hj ▸ rfl⟩
  have h := evaluate_relabel_reverse (pivotRelabel p)
    (List.ofFn (fun j : Fin V => AdjointStep.gate (idealWeightGate (rowWeight K p) j))) hg
  rw [h]
  rfl

/-- The ideal setup word sends `Ket p` to the square-root transition-row state `generalRowState
K p`. -/
theorem generalIdealSetupWord_exact {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    evaluate 1 (generalIdealSetupWord K p) *ᵥ Ket p = generalRowState K p := by
  rw [generalIdealSetupWord_evaluate, relabelGate_mulVec_apply]
  rw [relabelState_pivotRelabel_symm_ket]
  obtain ⟨hu, huMass, hket⟩ := rational_weight_ideal_preparation_exact V
    (rowWeight K p) (rowWeight_nonneg K p) (by
      rw [rowWeight_mass_one]
      exact_mod_cast (by norm_num : (0 : ℝ) < 1))
  rw [huMass]
  exact (generalRowState_eq_relabel K p).symm

/-- The computed setup evaluation differs from ideal pivot-relabelled preparation by at most `32
* V / 2^k` in operator norm. -/
theorem generalSetupWord_matrix_error {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (k : ℕ) :
    ‖evaluate 1 (generalSetupWord K p k)
        - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p))‖
      ≤ 32 * (V : ℝ) / 2 ^ k := by
  rw [generalSetupWord_evaluate]
  rw [l2_norm_relabelGate_sub]
  obtain ⟨hWF, hU, herr⟩ := rational_weight_numerical_word_unitary_and_error V k
    (rowWeight K p) (rowWeight_nonneg K p)
  exact herr

/-- On `Ket p`, the difference between computed and ideal setup has Euclidean norm at most `32 *
V / 2^k`. -/
theorem generalSetupWord_state_error {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (k : ℕ) :
    ‖toEuclidean_fromVec
        (((evaluate 1 (generalSetupWord K p k)
            - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
          *ᵥ Ket p))‖
      ≤ 32 * (V : ℝ) / 2 ^ k := by
  have h1 := l2_norm_mulVec_fromVec_le
    ((evaluate 1 (generalSetupWord K p k)
      - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))) (Ket p)
  have hket : ‖toEuclidean_fromVec (Ket p)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec (Ket p)).mp (normalized_ket p)
  rw [hket] at h1
  obtain ⟨hWF, hU, herr⟩ := rational_weight_numerical_word_unitary_and_error V k
    (rowWeight K p) (rowWeight_nonneg K p)
  calc
    _ ≤ ‖(evaluate 1 (generalSetupWord K p k)
        - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))‖ * 1 := h1
    _ = ‖relabelGate (pivotRelabel p) (rationalWeightPrepare (rowWeight K p) k)
        - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p))‖ * 1 := by
      rw [generalSetupWord_evaluate]
    _ = ‖rationalWeightPrepare (rowWeight K p) k
        - idealWeightPrepare (rowWeight K p)‖ * 1 := by
      rw [l2_norm_relabelGate_sub]
    _ = ‖rationalWeightPrepare (rowWeight K p) k
        - idealWeightPrepare (rowWeight K p)‖ := by
      rw [mul_one]
    _ ≤ 32 * (V : ℝ) / 2 ^ k := herr

/-- An adjoint word containing only fixed gates has zero query count. -/
theorem adjointQueryCount_of_gates {H : Type*} (cs : List (AdjointStep H))
    (hg : ∀ c ∈ cs, ∃ V, c = AdjointStep.gate V) : adjointQueryCount cs = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨V, rfl⟩ := hg c (by simp)
    have hgs : ∀ c' ∈ cs, ∃ V', c' = AdjointStep.gate V' := by
      intro c' hc'
      exact hg c' (by simp [hc'])
    simp [adjointQueryCount, ih hgs]

/-- An adjoint word containing only fixed gates has gate count equal to its length. -/
theorem adjointGateCount_of_gates {H : Type*} (cs : List (AdjointStep H))
    (hg : ∀ c ∈ cs, ∃ V, c = AdjointStep.gate V) : adjointGateCount cs = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨V, rfl⟩ := hg c (by simp)
    have hgs : ∀ c' ∈ cs, ∃ V', c' = AdjointStep.gate V' := by
      intro c' hc'
      exact hg c' (by simp [hc'])
    simp [adjointGateCount, ih hgs]

/-- The computed setup word uses zero queries and `V` gates, while its rational weight
computation makes `2 * V * k` comparisons. -/
theorem generalSetupWord_costs {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) (k : ℕ) :
    adjointQueryCount (generalSetupWord K p k) = 0 ∧
    adjointGateCount (generalSetupWord K p k) = V ∧
    rationalWeightComparisons (rowWeight K p) k = 2 * V * k := by
  have hgl : ∀ c ∈ (List.ofFn (fun j : Fin V => AdjointStep.gate
        (relabelGate (pivotRelabel p) (rationalWeightGate (rowWeight K p) k j)))),
      ∃ V', c = AdjointStep.gate V' := by
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hc
    exact ⟨relabelGate (pivotRelabel p) (rationalWeightGate (rowWeight K p) k j), hj ▸ rfl⟩
  have hgr : ∀ c ∈ (List.ofFn (fun j : Fin V => AdjointStep.gate
        (relabelGate (pivotRelabel p) (rationalWeightGate (rowWeight K p) k j)))).reverse,
      ∃ V', c = AdjointStep.gate V' := by
    intro c hc
    refine hgl c ?_
    rw [List.mem_reverse] at hc
    exact hc
  rw [generalSetupWord_eq]
  refine ⟨adjointQueryCount_of_gates _ hgr, ?_, ?_⟩
  · rw [adjointGateCount_of_gates _ hgr]
    simp [List.length_reverse, List.length_ofFn]
  · obtain ⟨hRange, hlen, hcomp⟩ :=
      rational_weight_data_ranges_and_actual_comparisons V k (rowWeight K p)
        (rowWeight_nonneg K p)
    exact hcomp

/-- The list of further graph-access components beyond the row-setup realization and cost
guarantees established here. -/
def generalGraphAccessResidual : List String :=
  [ "the graph-local update word (the neighbour row map) is not built here",
    "the graph-local check word (the marked predicate) is not built here",
    "the effective S/U/C account with finite-gate, bit-time and space ledgers is not built here",
    "the intertwining with the double-frame source oracle is not built here",
    "the realised reachable-spectrum statement is not built here" ]

/-- A proposition collecting computed setup legality, ideal row realization, operator and state
error bounds, and exact query, gate, and comparison counts. -/
structure GeneralGraphSetupAccount (V : ℕ) (K : GeneralKernel V) (p : GeneralVertex V)
    (k : ℕ) : Prop where

  legal : WellFormedAdjointCircuit (generalSetupWord K p k)

  exactRealisation : evaluate 1 (generalIdealSetupWord K p) *ᵥ Ket p = generalRowState K p

  operatorError :
    ‖evaluate 1 (generalSetupWord K p k)
        - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p))‖
      ≤ 32 * (V : ℝ) / 2 ^ k

  stateError :
    ‖toEuclidean_fromVec
        (((evaluate 1 (generalSetupWord K p k)
            - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
          *ᵥ Ket p))‖
      ≤ 32 * (V : ℝ) / 2 ^ k

  queries : adjointQueryCount (generalSetupWord K p k) = 0

  gates : adjointGateCount (generalSetupWord K p k) = V

  comparisons : rationalWeightComparisons (rowWeight K p) k = 2 * V * k

/-- The row-setup construction satisfies every realization, approximation, and cost field of
`GeneralGraphSetupAccount`. -/
theorem clause37_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) (k : ℕ) :
    GeneralGraphSetupAccount V K p k := by
  obtain ⟨hQ, hG, hC⟩ := generalSetupWord_costs K p k
  exact ⟨generalSetupWord_wellFormed K p k, generalIdealSetupWord_exact K p,
    generalSetupWord_matrix_error K p k, generalSetupWord_state_error K p k,
    hQ, hG, hC⟩

end GeneralWalkAccess
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
