/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairWordSemanticsStat
set_option warningAsError false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.GateCore

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Concepts.SearchStopping.GateCore Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

theorem haar_source_counts (C : Circuit (I × Bool)) :
    preparedDataQueries (C.reverse.map aqHaarPreparedOfStep) = QueryCount C ∧
    preparedInputQueries (C.reverse.map aqHaarPreparedOfStep) = 0 ∧
    preparedFixedGates (C.reverse.map aqHaarPreparedOfStep) = GateCount C := by
  induction C with
  | nil => trivial
  | cons s C ih =>
    simp only [List.map_reverse] at ih
    cases s <;> simp [List.reverse_cons, List.map_append, preparedCounts_append,
      aqHaarPreparedOfStep, preparedDataQueries, preparedInputQueries,
      preparedFixedGates, QueryCount, GateCount, ih.1, ih.2.1, ih.2.2]

theorem haar_source_eval (U B : Matrix (I × Bool) (I × Bool) ℂ)
    (C : Circuit (I × Bool)) (ψ : QState (I × Bool)) :
    evaluatePrepared U B (C.reverse.map aqHaarPreparedOfStep) *ᵥ ψ = Run U C ψ := by
  induction C generalizing ψ with
  | nil => simp [evaluatePrepared, Run]
  | cons s C ih =>
    cases s <;> simp only [List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, evaluatePrepared_append, evaluatePrepared, aqHaarPreparedOfStep,
      preparedInstruction, Matrix.mul_one, ← Matrix.mulVec_mulVec, ih, Run, ApplyGate]

theorem haar_source_valid (C : Circuit (I × Bool)) (hC : IsUnitaryCircuit C) :
    PreparedCircuitValid (C.reverse.map aqHaarPreparedOfStep) := by
  intro c hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  have hs' : s ∈ C := List.mem_reverse.mp hs
  cases s with
  | gate V => exact hC V hs'
  | query => trivial

theorem haar_pair_setOracle (E : Finset I) :
    PhaseOracle (fun z : I × Bool => decide (z.1 ∈ E)) = SetOracle (aqHaarPairMarked E) := by
  simp only [SetOracle, aqHaarPairMarked, Finset.mem_filter, Finset.mem_univ, true_and]

theorem haarPairWordSemantics : HaarPairWordSemantics := by
  intro I _ _ T' seed hT hprep j
  haveI : Nonempty (I × Bool) := ⟨seed⟩
  have hN : 0 < Fintype.card (I × Bool) := Fintype.card_pos
  have hsource := section6SourceGateSubgoal (I × Bool) hN T' (Ket seed)
    hT (normalized_ket seed) hprep (∅ : Finset (I × Bool)) j
  have hmap := haar_source_valid _ hsource.1
  have hH : TensorGate (1 : Matrix I I ℂ) Hadamard ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup I ℂ).one_mem hadamard_unitary
  have happ (cs ds : List (PreparedStep (I × Bool)))
      (hc : PreparedCircuitValid cs) (hd : PreparedCircuitValid ds) :
      PreparedCircuitValid (cs ++ ds) := by
    intro c h
    exact (List.mem_append.mp h).elim (hc c) (hd c)
  have hvalid : PreparedCircuitValid (aqHaarPairWord T' seed j) := by
    unfold aqHaarPairWord
    apply happ _ _
    · apply happ _ _ _ hmap
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hH
      · trivial
    · intro c hc
      have he : c = .gate T' := List.mem_singleton.mp hc
      subst c
      exact hT
  have hcounts := haar_source_counts (SourceGateCircuit T' (Ket seed) j)
  simp only [List.map_reverse] at hcounts
  have hgate : GateCount (SourceGateCircuit T' (Ket seed) j) = j := by
    simp [SourceGateCircuit, SourceGateBlock, gateCount_repeatCircuit, GateCount]
  have hcountWord : preparedDataQueries (aqHaarPairWord T' seed j) = j ∧
      preparedInputQueries (aqHaarPairWord T' seed j) = 1 ∧
      preparedFixedGates (aqHaarPairWord T' seed j) = j+2 := by
    simp [aqHaarPairWord, preparedCounts_append, hcounts.1, hcounts.2.1, hcounts.2.2,
      hsource.2.1, hgate, preparedDataQueries, preparedInputQueries, preparedFixedGates,
      Nat.add_comm]
    omega
  refine ⟨hvalid, hcountWord.1, hcountWord.2.1, hcountWord.2.2, ?_⟩
  intro E S
  constructor
  · have hs := section6SourceGateSubgoal (I × Bool) hN T' (Ket seed)
      hT (normalized_ket seed) hprep (aqHaarPairMarked E) j
    simp only [aqHaarPairOutput, aqHaarPairWord, evaluatePrepared_append,
      evaluatePrepared, preparedInstruction, Matrix.mul_one, ← Matrix.mulVec_mulVec,
      hprep, haar_source_eval, haar_pair_setOracle E, hs.2.2.1]
  · exact normalized_applyGate
      (hvalid.evaluate_unitary (phaseOracle_unitary _) (phaseOracle_unitary S))
      (normalized_ket seed)

end Qatlib.Concepts.AmpTransform.HaarPairTest
