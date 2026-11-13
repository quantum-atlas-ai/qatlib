/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.GateVocab.QueryFrame
import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput

/-!
# Compiling phase queries into Boolean queries

`sourcePhaseToBitWord` surrounds each query by a Hadamard change of basis on the Boolean
register. The compiler preserves the run and measurement probabilities, preserves query count,
and adds two gates per query. The mathematical context is [BrassardHoyerTapp1998Counting].

## Main statements

* `source_phase_to_bit_run`: Running the compiled word with the bit oracle equals running the
  original word with the phase oracle on the same input state.
* `source_phase_to_bit_gates`: The phase-to-bit compiler adds exactly two gates per query.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

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

/-- The Hadamard frame on the Boolean query register squares to the identity. -/
theorem source_frame_involution :
    (controlHadamard (I := I) (W := W)) * controlHadamard = 1 := by
  simp only [controlHadamard,tensorGate_mul,Matrix.one_mul,hadamard_mul_self,tensorGate_one]

/-- The Hadamard frame on the Boolean query register is unitary. -/
theorem source_frame_unitary :
    controlHadamard (I := I) (W := W) ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Matrix.unitaryGroup I ℂ).one_mem hadamard_unitary)
    (Matrix.unitaryGroup W ℂ).one_mem

/-- Conjugating the workspace phase oracle by the Boolean-register Hadamard frame yields the
workspace bit oracle. -/
theorem source_hadamard_phase_bit (f : I → Bool) :
    (controlHadamard (I := I) (W := W)) * workspacePhaseOracle f * controlHadamard =
      workspaceBitOracle f := by
  apply Matrix.ext_iff_mulVec.mpr
  intro psi
  have h := run_bitToPhaseCircuitSameInput f [Step.query] psi
  simpa [bitToPhaseCircuitSameInput,bitToPhaseStep,Run,ApplyGate,Matrix.mulVec_mulVec,
    Matrix.mul_assoc] using h

/-- Conjugating the workspace bit oracle by the Boolean-register Hadamard frame yields the
workspace phase oracle. -/
theorem source_hadamard_bit_phase (f : I → Bool) :
    (controlHadamard (I := I) (W := W)) * workspaceBitOracle f * controlHadamard =
      workspacePhaseOracle f := by
  rw [← source_hadamard_phase_bit]
  calc
    _ = (controlHadamard * controlHadamard) * workspacePhaseOracle f *
        (controlHadamard * controlHadamard) := by noncomm_ring
    _ = _ := by rw [source_frame_involution,Matrix.one_mul,Matrix.mul_one]

/-- Compile a phase-query circuit by inserting the Boolean-register Hadamard frame around every
query. -/
def sourcePhaseToBitWord (C : Circuit ((I × Bool) × W)) : Circuit ((I × Bool) × W) :=
  queryFrame controlHadamard C

/-- Running the compiled word with the bit oracle equals running the original word with the
phase oracle on the same input state. -/
theorem source_phase_to_bit_run (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (psi : QState ((I × Bool) × W)) :
    Run (workspaceBitOracle f) (sourcePhaseToBitWord C) psi = Run (workspacePhaseOracle f) C psi := by
  rw [sourcePhaseToBitWord,queryFrame_run,source_hadamard_bit_phase]

section
omit [Fintype I] [Fintype W]

/-- The phase-to-bit compiler preserves the number of queries. -/
theorem source_phase_to_bit_queries (C : Circuit ((I × Bool) × W)) :
    QueryCount (sourcePhaseToBitWord C) = QueryCount C := queryFrame_queries _ C

/-- The phase-to-bit compiler adds exactly two gates per query. -/
theorem source_phase_to_bit_gates (C : Circuit ((I × Bool) × W)) :
    GateCount (sourcePhaseToBitWord C) = GateCount C + 2*QueryCount C := queryFrame_gates _ C

end

/-- Compiling a unitary circuit by the phase-to-bit compiler produces a unitary circuit. -/
theorem source_phase_to_bit_unitary (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (sourcePhaseToBitWord C) := queryFrame_unitary _ source_frame_unitary C hC

/-- The compiled bit-oracle run and the original phase-oracle run assign the same probability to
every measurement event. -/
theorem source_phase_to_bit_readout (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (psi : QState ((I × Bool) × W)) (S : Finset ((I × Bool) × W)) :
    MeasureProb (Run (workspaceBitOracle f) (sourcePhaseToBitWord C) psi) S =
      MeasureProb (Run (workspacePhaseOracle f) C psi) S := by
  rw [source_phase_to_bit_run]

end Qatlib.Papers.QCounting98.MainResults.BooleanCompiler
