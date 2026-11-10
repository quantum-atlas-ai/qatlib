/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.GateVocab.QueryFrame
import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.BooleanCompiler
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.GateVocabulary.GateVocab
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem source_frame_involution :
    (controlHadamard (I := I) (W := W)) * controlHadamard = 1 := by
  simp only [controlHadamard,tensorGate_mul,Matrix.one_mul,hadamard_mul_self,tensorGate_one]

theorem source_frame_unitary :
    controlHadamard (I := I) (W := W) ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Matrix.unitaryGroup I ℂ).one_mem hadamard_unitary)
    (Matrix.unitaryGroup W ℂ).one_mem

theorem source_hadamard_phase_bit (f : I → Bool) :
    (controlHadamard (I := I) (W := W)) * workspacePhaseOracle f * controlHadamard =
      workspaceBitOracle f := by
  apply Matrix.ext_iff_mulVec.mpr
  intro psi
  have h := run_bitToPhaseCircuitSameInput f [Step.query] psi
  simpa [bitToPhaseCircuitSameInput,bitToPhaseStep,Run,ApplyGate,Matrix.mulVec_mulVec,
    Matrix.mul_assoc] using h

theorem source_hadamard_bit_phase (f : I → Bool) :
    (controlHadamard (I := I) (W := W)) * workspaceBitOracle f * controlHadamard =
      workspacePhaseOracle f := by
  rw [← source_hadamard_phase_bit]
  calc
    _ = (controlHadamard * controlHadamard) * workspacePhaseOracle f *
        (controlHadamard * controlHadamard) := by noncomm_ring
    _ = _ := by rw [source_frame_involution,Matrix.one_mul,Matrix.mul_one]

def sourcePhaseToBitWord (C : Circuit ((I × Bool) × W)) : Circuit ((I × Bool) × W) :=
  queryFrame controlHadamard C

theorem source_phase_to_bit_run (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (psi : QState ((I × Bool) × W)) :
    Run (workspaceBitOracle f) (sourcePhaseToBitWord C) psi = Run (workspacePhaseOracle f) C psi := by
  rw [sourcePhaseToBitWord,queryFrame_run,source_hadamard_bit_phase]

section
omit [Fintype I] [Fintype W]

theorem source_phase_to_bit_queries (C : Circuit ((I × Bool) × W)) :
    QueryCount (sourcePhaseToBitWord C) = QueryCount C := queryFrame_queries _ C

theorem source_phase_to_bit_gates (C : Circuit ((I × Bool) × W)) :
    GateCount (sourcePhaseToBitWord C) = GateCount C + 2*QueryCount C := queryFrame_gates _ C

end

theorem source_phase_to_bit_unitary (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (sourcePhaseToBitWord C) := queryFrame_unitary _ source_frame_unitary C hC

theorem source_phase_to_bit_readout (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (psi : QState ((I × Bool) × W)) (S : Finset ((I × Bool) × W)) :
    MeasureProb (Run (workspaceBitOracle f) (sourcePhaseToBitWord C) psi) S =
      MeasureProb (Run (workspacePhaseOracle f) C psi) S := by
  rw [source_phase_to_bit_run]

end Qatlib.Papers.QCounting98.MainResults.BooleanCompiler
