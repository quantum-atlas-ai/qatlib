/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCounting98.MainResults.BooleanCompiler
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport

/-!
# Transport of counting circuits to Boolean oracles

This module reorders the phase, control, and data labels using `aeStandardLabels` and compiles
controlled marked-set phase queries into Boolean workspace queries through `standardAEWord`. The
construction connects the amplitude-estimation circuit vocabulary to the Boolean-oracle
implementation of [BrassardHoyerTapp1998Counting].

The transport preserves circuit execution up to state relabeling, readout probabilities, query
count, and unitarity. Its fixed-gate count increases by two per query.

## Main statements

* `source_controlled_mark_relabel`: the relabeled controlled marking gate is the workspace phase
  oracle.
* `standardAE_run`: execution agrees after state relabeling.
* `standardAE_gates`: the compilation adds two fixed gates per query.
* `standardAE_readout`: corresponding events have equal measurement probabilities.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

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

/-- The equivalence sending phase-first labels `(z, (b, i))` to workspace labels `((i, b), z)`. -/
def aeStandardLabels (I : Type) (M : ℕ) : (Fin M × (Bool × I)) ≃ ((I × Bool) × Fin M) where
  toFun p := ((p.2.2,p.2.1),p.1)
  invFun p := (p.2,(p.1.2,p.1.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite set of indices where the Boolean marking function `f` is true. -/
def sourceMarked {I : Type} [Fintype I] (f : I → Bool) : Finset I :=
  Finset.univ.filter (fun i => f i = true)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Relabeling the controlled marked-set phase gate by `aeStandardLabels` gives the Boolean
workspace phase oracle. -/
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

/-- The Boolean-oracle circuit obtained by relabeling an amplitude-estimation circuit and
compiling its phase queries into bit queries. -/
def standardAEWord (M : ℕ) (C : Circuit (Fin M × (Bool × I))) : Circuit ((I × Bool) × Fin M) :=
  sourcePhaseToBitWord (relabelCircuit (aeStandardLabels I M) C)

/-- Running the compiled circuit with the Boolean workspace oracle equals the relabeling of the
source circuit's execution with its controlled marking oracle. -/
theorem standardAE_run (M : ℕ) (f : I → Bool) (C : Circuit (Fin M × (Bool × I)))
    (psi : QState (Fin M × (Bool × I))) :
    Run (workspaceBitOracle f) (standardAEWord M C) (relabelState (aeStandardLabels I M) psi) =
      relabelState (aeStandardLabels I M) (Run (aeControlledGate M (preparedMark (sourceMarked f))) C psi) := by
  rw [standardAEWord,source_phase_to_bit_run,← source_controlled_mark_relabel]
  exact (run_relabelCircuit_readout (aeStandardLabels I M)
    (aeControlledGate M (preparedMark (sourceMarked f))) C psi ∅).1

/-- The compilation `standardAEWord` preserves the number of oracle queries. -/
theorem standardAE_queries (M : ℕ) (C : Circuit (Fin M × (Bool × I))) :
    QueryCount (standardAEWord M C) = QueryCount C := by
  rw [standardAEWord,source_phase_to_bit_queries]
  exact (relabelCircuit_legality_resources (aeStandardLabels I M) C).2.1

/-- The fixed-gate count of `standardAEWord M C` is `GateCount C + 2 * QueryCount C`. -/
theorem standardAE_gates (M : ℕ) (C : Circuit (Fin M × (Bool × I))) :
    GateCount (standardAEWord M C) = GateCount C + 2*QueryCount C := by
  rw [standardAEWord,source_phase_to_bit_gates]
  have h := relabelCircuit_legality_resources (aeStandardLabels I M) C
  rw [h.2.1,h.2.2.1]

/-- The compilation `standardAEWord` preserves the property of being a unitary circuit. -/
theorem standardAE_unitary (M : ℕ) (C : Circuit (Fin M × (Bool × I))) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (standardAEWord M C) := by
  apply source_phase_to_bit_unitary
  exact (relabelCircuit_legality_resources (aeStandardLabels I M) C).1.mpr hC

/-- The compiled Boolean-oracle circuit and the source controlled-marking circuit give equal
probabilities to events related by `aeStandardLabels`. -/
theorem standardAE_readout (M : ℕ) (f : I → Bool) (C : Circuit (Fin M × (Bool × I)))
    (psi : QState (Fin M × (Bool × I))) (S : Finset (Fin M × (Bool × I))) :
    MeasureProb (Run (workspaceBitOracle f) (standardAEWord M C) (relabelState (aeStandardLabels I M) psi))
      (S.map (aeStandardLabels I M).toEmbedding) =
        MeasureProb (Run (aeControlledGate M (preparedMark (sourceMarked f))) C psi) S := by
  rw [standardAEWord,source_phase_to_bit_run,← source_controlled_mark_relabel]
  exact (run_relabelCircuit_readout (aeStandardLabels I M)
    (aeControlledGate M (preparedMark (sourceMarked f))) C psi S).2

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
