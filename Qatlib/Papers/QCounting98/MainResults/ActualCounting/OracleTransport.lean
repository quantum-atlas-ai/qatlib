/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.BooleanCompiler
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Papers.QCounting98.MainResults.BooleanCompiler
open scoped Classical BigOperators

def aeStandardLabels (I : Type) (M : ℕ) : (Fin M × (Bool × I)) ≃ ((I × Bool) × Fin M) where
  toFun p := ((p.2.2,p.2.1),p.1)
  invFun p := (p.2,(p.1.2,p.1.1))
  left_inv _ := rfl
  right_inv _ := rfl

def sourceMarked {I : Type} [Fintype I] (f : I → Bool) : Finset I :=
  Finset.univ.filter (fun i => f i = true)

variable {I : Type} [Fintype I] [DecidableEq I]

theorem source_controlled_mark_relabel (M : ℕ) (f : I → Bool) :
    relabelGate (aeStandardLabels I M) (aeControlledGate M (preparedMark (sourceMarked f))) =
      workspacePhaseOracle f := by
  rw [preparedMark_eq_diagonal]
  ext ⟨⟨i,b⟩,z⟩ ⟨⟨j,c⟩,w⟩
  simp only [relabelGate,Matrix.reindex_apply,aeStandardLabels,aeControlledGate,TensorGate,
    Matrix.kronecker_apply,controlOracle,select,workspacePhaseOracle,
    PhaseOracle,Matrix.diagonal_apply,sourceMarked,Finset.mem_filter,Finset.mem_univ,true_and,
    Matrix.one_apply]
  by_cases hij : i = j <;> by_cases hzw : z = w <;> cases b <;> cases c <;> simp_all

def standardAEWord (M : ℕ) (C : Circuit (Fin M × (Bool × I))) : Circuit ((I × Bool) × Fin M) :=
  sourcePhaseToBitWord (relabelCircuit (aeStandardLabels I M) C)

theorem standardAE_run (M : ℕ) (f : I → Bool) (C : Circuit (Fin M × (Bool × I)))
    (psi : QState (Fin M × (Bool × I))) :
    Run (workspaceBitOracle f) (standardAEWord M C) (relabelState (aeStandardLabels I M) psi) =
      relabelState (aeStandardLabels I M) (Run (aeControlledGate M (preparedMark (sourceMarked f))) C psi) := by
  rw [standardAEWord,source_phase_to_bit_run,← source_controlled_mark_relabel]
  exact (run_relabelCircuit_readout (aeStandardLabels I M)
    (aeControlledGate M (preparedMark (sourceMarked f))) C psi ∅).1

theorem standardAE_queries (M : ℕ) (C : Circuit (Fin M × (Bool × I))) :
    QueryCount (standardAEWord M C) = QueryCount C := by
  rw [standardAEWord,source_phase_to_bit_queries]
  exact (relabelCircuit_legality_resources (aeStandardLabels I M) C).2.1

theorem standardAE_gates (M : ℕ) (C : Circuit (Fin M × (Bool × I))) :
    GateCount (standardAEWord M C) = GateCount C + 2*QueryCount C := by
  rw [standardAEWord,source_phase_to_bit_gates]
  have h := relabelCircuit_legality_resources (aeStandardLabels I M) C
  rw [h.2.1,h.2.2.1]

theorem standardAE_unitary (M : ℕ) (C : Circuit (Fin M × (Bool × I))) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (standardAEWord M C) := by
  apply source_phase_to_bit_unitary
  exact (relabelCircuit_legality_resources (aeStandardLabels I M) C).1.mpr hC

theorem standardAE_readout (M : ℕ) (f : I → Bool) (C : Circuit (Fin M × (Bool × I)))
    (psi : QState (Fin M × (Bool × I))) (S : Finset (Fin M × (Bool × I))) :
    MeasureProb (Run (workspaceBitOracle f) (standardAEWord M C) (relabelState (aeStandardLabels I M) psi))
      (S.map (aeStandardLabels I M).toEmbedding) =
        MeasureProb (Run (aeControlledGate M (preparedMark (sourceMarked f))) C psi) S := by
  rw [standardAEWord,source_phase_to_bit_run,← source_controlled_mark_relabel]
  exact (run_relabelCircuit_readout (aeStandardLabels I M)
    (aeControlledGate M (preparedMark (sourceMarked f))) C psi S).2

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
