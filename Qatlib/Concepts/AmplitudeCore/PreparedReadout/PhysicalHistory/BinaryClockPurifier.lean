/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPhysicalTime
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.TensorResidual

/-!
# Purification registers for the physical clock simulator

This module extends the physical-time simulator by an untouched purification environment.
`lift`, `instructions`, `oracle`, `initialFrame`, and `target` tensor their original matrices
with the environment identity.

The resulting full-state error applies to entangled inputs and retains the original query and
gate counts, as expected from the tensor-register formalism of [NielsenChuang2010].

## Main statements

* `full_output_error`: the framed error bound remains valid with a purification environment.
* `resources`: tensor extension preserves the physical-time resource counts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPurifier

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical Kronecker Matrix.Norms.L2Operator

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

noncomputable local instance executionDecidableEq (q : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q W) := BinaryClockSingleCU.newDecidableEq q W

/-- The operator norm error of the physical-time simulator on its initial frame is at most
`(q+1)*2⁻ᵏ`. -/
theorem operator_error (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hα : 0 < α) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U F F) :
    ‖evaluate (BinaryClockSingleCU.oracle q U)
        (BinaryClockPhysicalTime.instructions q F α T k) * BinaryClockPhysicalTime.initialFrame q F -
      BinaryClockPhysicalTime.initialFrame q F * BinaryClockPhysicalTime.physicalTarget q H T‖ ≤
      ((q + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k := by
  apply TensorResidual.operator_error_of_full_output _ _ _ _ (by positivity)
  exact BinaryClockPhysicalTime.full_output_error q α T k H U F hα hH h

section Purifier

variable {E : Type} [Fintype E] [DecidableEq E]

/-- Extend a simulator matrix by the identity on the purification environment using a Kronecker
product. -/
noncomputable def lift (q : ℕ) (M : Matrix (BinaryClockSingleCU.New q W)
    (BinaryClockSingleCU.New q W) ℂ) :
    Matrix (BinaryClockSingleCU.New q W × E) (BinaryClockSingleCU.New q W × E) ℂ :=
  M ⊗ₖ (1 : Matrix E E ℂ)

omit [Fintype W] [Fintype E] in

/-- Extending the identity simulator matrix gives the identity on the enlarged register. -/
private theorem lift_one (q : ℕ) : lift (W := W) (E := E) q 1 = 1 :=
  Matrix.one_kronecker_one

omit [DecidableEq W] in

/-- Extending simulator matrices by the environment identity preserves matrix multiplication. -/
private theorem lift_mul (q : ℕ) (M N : Matrix (BinaryClockSingleCU.New q W)
    (BinaryClockSingleCU.New q W) ℂ) : lift (E := E) q (M * N) = lift q M * lift q N := by
  simp only [lift, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

omit [Fintype W] [DecidableEq W] [Fintype E] in

/-- Extending a simulator matrix by the environment identity commutes with conjugate transpose. -/
private theorem lift_adjoint (q : ℕ) (M : Matrix (BinaryClockSingleCU.New q W)
    (BinaryClockSingleCU.New q W) ℂ) : lift (E := E) q Mᴴ = (lift q M)ᴴ := by
  simp only [lift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- Lift every gate in the physical-time simulation word to the register containing the
purification environment. -/
noncomputable def instructions (q : ℕ) (F : Matrix W I ℂ) (α T : ℚ) (k : ℕ) :
    List (AdjointStep (BinaryClockSingleCU.New q W × E)) :=
  phaseLiftWord (lift q) (BinaryClockPhysicalTime.instructions q F α T k)

/-- The single controlled-oracle matrix extended by the identity on the purification
environment. -/
noncomputable def oracle (q : ℕ) (U : Matrix W W ℂ) :
    Matrix (BinaryClockSingleCU.New q W × E) (BinaryClockSingleCU.New q W × E) ℂ :=
  lift q (BinaryClockSingleCU.oracle q U)

/-- The physical-time initial frame extended by the identity on the purification environment. -/
noncomputable def initialFrame (q : ℕ) (F : Matrix W I ℂ) :
    Matrix (BinaryClockSingleCU.New q W × E) ((Reg q × I) × E) ℂ :=
  BinaryClockPhysicalTime.initialFrame q F ⊗ₖ (1 : Matrix E E ℂ)

/-- The physical midpoint target extended by the identity on the purification environment. -/
noncomputable def target (q : ℕ) (H : Matrix I I ℂ) (T : ℚ) :
    Matrix ((Reg q × I) × E) ((Reg q × I) × E) ℂ :=
  BinaryClockPhysicalTime.physicalTarget q H T ⊗ₖ (1 : Matrix E E ℂ)

/-- Evaluating the purified instruction word gives the identity extension of the original
physical-time evaluation. -/
theorem evaluate_matrix (q : ℕ) (U : Matrix W W ℂ) (F : Matrix W I ℂ)
    (α T : ℚ) (k : ℕ) :
    evaluate (oracle (E := E) q U) (instructions q F α T k) =
      lift q (evaluate (BinaryClockSingleCU.oracle q U)
        (BinaryClockPhysicalTime.instructions q F α T k)) :=
  phaseLiftWord_evaluate (lift q) (lift_one q) (lift_mul q) (lift_adjoint q)
    (BinaryClockSingleCU.oracle q U) (BinaryClockPhysicalTime.instructions q F α T k)

/-- The purified initial frame is an isometry under the stated Hermitian encoding assumptions. -/
theorem initialFrame_isometry (q : ℕ) (α : ℚ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U F F) :
    IsIsometry (initialFrame (E := E) q F) :=
  TensorResidual.tensor_frame_isometry _
    (BinaryClockPhysicalTime.initialFrame_isometry q α H U F hH h)

/-- For any input entangled with the environment, the framed output error is at most `(q+1)*2⁻ᵏ`
times its Euclidean norm. -/
theorem full_output_error (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hα : 0 < α) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U F F)
    (Ψ : QState ((Reg q × I) × E)) :
    ‖toEuclidean_fromVec
      (evaluate (oracle q U) (instructions q F α T k) *ᵥ (initialFrame q F *ᵥ Ψ) -
        initialFrame q F *ᵥ (target q H T *ᵥ Ψ))‖ ≤
      (((q + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) * ‖toEuclidean_fromVec Ψ‖ := by
  rw [evaluate_matrix]
  exact TensorResidual.tensor_full_output_error _ _ _ _
    (operator_error q α T k H U F hα hH h) Ψ

/-- The purified word is well formed and has the same query and gate counts as the physical-time
word. -/
theorem resources (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U F F) :
    WellFormedAdjointCircuit (instructions (E := E) q F α T k) ∧
      adjointQueryCount (instructions (E := E) q F α T k) =
        adjointQueryCount (BinaryClockPhysicalTime.instructions q F α T k) ∧
      adjointGateCount (instructions (E := E) q F α T k) =
        adjointGateCount (BinaryClockPhysicalTime.instructions q F α T k) := by
  have hw := (BinaryClockPhysicalTime.resources q α T k H U F hH h).1
  exact ⟨phaseLiftWord_wellFormed (lift q)
    (fun _ hM => tensorGate_unitary hM (Submonoid.one_mem _)) hw,
    phaseLiftWord_counts (lift (E := E) q) _⟩

/-- The adjoint purified word is well formed and retains the physical-time word's query and gate
counts. -/
theorem inverse_resources (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U F F) :
    WellFormedAdjointCircuit (adjointCircuit (instructions (E := E) q F α T k)) ∧
      adjointQueryCount (adjointCircuit (instructions (E := E) q F α T k)) =
        adjointQueryCount (BinaryClockPhysicalTime.instructions q F α T k) ∧
      adjointGateCount (adjointCircuit (instructions (E := E) q F α T k)) =
        adjointGateCount (BinaryClockPhysicalTime.instructions q F α T k) := by
  have hr := resources (E := E) q α T k H U F hH h
  exact ⟨hr.1.adjointCircuit, (adjointQueryCount_adjointCircuit _).trans hr.2.1,
    (adjointGateCount_adjointCircuit _).trans hr.2.2⟩

end Purifier

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPurifier
