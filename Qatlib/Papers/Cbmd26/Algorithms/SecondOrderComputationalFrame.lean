/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.SecondOrderDecodedWord
import Qatlib.Papers.Cbmd26.Algorithms.StaticComputationalFrame

/-!
# Computational Success Frames for Second-Order Circuits

`secondOrderComputationalEquiv` separates the system register from `SecondOrderAncillas`, and
`secondOrderCleanAncilla` specifies the clean ancilla value. This identifies
`secondOrderDecodedFrame` with a computational tag and `secondOrderSuccessEvent` with its
measurement event.

`secondOrderInputLift` applies a system preparation gate uniformly over the ancillas. The
resulting preparation and projector identities connect the decoded second-order CBMD circuits
associated with the cited paper to computational-basis input and success measurements. See
[WangEtAl2026].

## Main statements

* `secondOrderDecodedFrame_computational` identifies the decoded frame with a reindexed
  computational tag.
* `secondOrderDecodedFrame_rangeProjector` identifies its range projector with the projector of
  `secondOrderSuccessEvent`.
* `secondOrderInputLift_unitary` preserves unitarity of an input gate.
* `secondOrderInputLift_prepare` prepares the decoded-frame state from the specified clean basis
  state.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

section SecondOrder
variable {J Anc I : Type} [Fintype J] [DecidableEq J] [Fintype Anc] [DecidableEq Anc]
  [Fintype I] [DecidableEq I]
local instance cbmdSecondOrderComputationalFrameInstance1 : DecidableEq (PreparedPredicateLabels (Fin 4) J Bool) :=
  inferInstanceAs (DecidableEq ((Fin 4 × J) × (Bool × Bool)))

/-- The ancilla register combining the outer Boolean control, prepared predicate labels, and
original encoding ancilla for the second-order circuit. -/
abbrev SecondOrderAncillas (J Anc : Type) := Bool × (PreparedPredicateLabels (Fin 4) J Bool × Anc)

/-- Reassociates the second-order workspace into the product of `SecondOrderAncillas` and the
system register. -/
def secondOrderComputationalEquiv : SecondOrderSpace J (Anc × I) ≃
    SecondOrderAncillas J Anc × I where
  toFun := fun ⟨b,l,a,i⟩ => ((b,l,a),i)
  invFun := fun ⟨⟨b,l,a⟩,i⟩ => (b,l,a,i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The clean second-order ancilla value with false control bits, branch zero, sample label
`j₀`, and original ancilla `a₀`. -/
def secondOrderCleanAncilla (j₀ : J) (a₀ : Anc) : SecondOrderAncillas J Anc :=
  (false,(((0,j₀),(false,false)),a₀))

/-- The computational-basis event whose separated ancilla register equals
`secondOrderCleanAncilla j₀ a₀`. -/
def secondOrderSuccessEvent (j₀ : J) (a₀ : Anc) :
    Finset (SecondOrderSpace J (Anc × I)) :=
  Finset.univ.filter fun p =>
    (secondOrderComputationalEquiv p).1 = secondOrderCleanAncilla j₀ a₀

/-- Lifts a system gate to the second-order workspace by applying it in parallel over all
separated ancilla values. -/
def secondOrderInputLift (B : Matrix I I ℂ) :
    Matrix (SecondOrderSpace J (Anc × I)) (SecondOrderSpace J (Anc × I)) ℂ :=
  (parallelOracle (J := SecondOrderAncillas J Anc) B).submatrix
    secondOrderComputationalEquiv secondOrderComputationalEquiv

omit [Fintype J] [Fintype Anc] [Fintype I] in

/-- For the computational original-ancilla frame, the second-order decoded frame is the
reindexed computational tag at the clean second-order ancilla value. -/
theorem secondOrderDecodedFrame_computational (j₀ : J) (a₀ : Anc) :
    secondOrderDecodedFrame j₀ (tagFrame a₀ (1 : Matrix I I ℂ)) =
      reindexFrame secondOrderComputationalEquiv
        (tagFrame (secondOrderCleanAncilla j₀ a₀) (1 : Matrix I I ℂ)) := by
  ext ⟨b,⟨⟨k,j⟩,c,d⟩,a,i⟩ l
  simp [secondOrderDecodedFrame, reindexFrame, preparedPredicateWorkspaceEquiv,
    secondOrderComputationalEquiv, secondOrderCleanAncilla, tagFrame,
    Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- The range projector of the computational second-order decoded frame equals the projector of
`secondOrderSuccessEvent`. -/
theorem secondOrderDecodedFrame_rangeProjector (j₀ : J) (a₀ : Anc) :
    rangeProjector (secondOrderDecodedFrame j₀ (tagFrame a₀ (1 : Matrix I I ℂ))) =
      Projector (secondOrderSuccessEvent (I := I) j₀ a₀) := by
  rw [secondOrderDecodedFrame_computational]
  change (tagFrame (secondOrderCleanAncilla j₀ a₀) (1 : Matrix I I ℂ)).submatrix
      secondOrderComputationalEquiv id *
    ((tagFrame (secondOrderCleanAncilla j₀ a₀) (1 : Matrix I I ℂ)).submatrix
      secondOrderComputationalEquiv id)ᴴ = _
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul]
  swap
  · exact Function.bijective_id
  change (rangeProjector (tagFrame (secondOrderCleanAncilla j₀ a₀)
    (1 : Matrix I I ℂ))).submatrix secondOrderComputationalEquiv
      secondOrderComputationalEquiv = _
  rw [computationalTag_rangeProjector]
  ext p q
  simp [Projector, Matrix.diagonal_apply, computationalTagEvent,
    secondOrderSuccessEvent]

/-- Lifting a unitary system gate to the second-order workspace preserves unitarity. -/
theorem secondOrderInputLift_unitary (B : Matrix I I ℂ)
    (hB : B ∈ Matrix.unitaryGroup I ℂ) :
    secondOrderInputLift (J := J) (Anc := Anc) B ∈
      Matrix.unitaryGroup (SecondOrderSpace J (Anc × I)) ℂ := by
  exact relabelGate_mem_unitary
    (parallelOracle_unitary (J := SecondOrderAncillas J Anc) hB)
    (secondOrderComputationalEquiv (J := J) (Anc := Anc) (I := I)).symm

/-- If `B` prepares `ψ` from basis state `i₀`, its second-order lift prepares the decoded-frame
embedding of `ψ` from the specified clean workspace basis state. -/
theorem secondOrderInputLift_prepare (B : Matrix I I ℂ) (j₀ : J) (a₀ : Anc) (i₀ : I)
    (ψ : QState I) (hB : ApplyGate B (Ket i₀) = ψ) :
    ApplyGate (secondOrderInputLift (J := J) (Anc := Anc) B)
      (Ket (false,(((0,j₀),(false,false)),(a₀,i₀)))) =
      secondOrderDecodedFrame j₀ (tagFrame a₀ (1 : Matrix I I ℂ)) *ᵥ ψ := by
  rw [secondOrderDecodedFrame_computational]
  ext p
  have h := congrFun (computationalTag_prepare B
    (secondOrderCleanAncilla j₀ a₀) i₀ ψ hB) (secondOrderComputationalEquiv p)
  simpa [ApplyGate, secondOrderInputLift, reindexFrame, Matrix.mulVec, dotProduct,
    secondOrderComputationalEquiv, secondOrderCleanAncilla, Ket,
    Fintype.sum_prod_type, parallelOracle, select] using! h
end SecondOrder
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
