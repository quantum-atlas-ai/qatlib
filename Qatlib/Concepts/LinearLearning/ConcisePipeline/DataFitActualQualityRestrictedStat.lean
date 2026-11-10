/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator
noncomputable def fitLeft {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Matrix (O⊕I) O ℂ := fun h o => if h=Sum.inl o then 1 else 0
noncomputable def fitRight {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Matrix (O⊕I) I ℂ := fun h i => if h=Sum.inr i then 1 else 0
def nativeRangeCoefficients (n : ℕ) : List ℚ := ratMulList [0,1] (nativeReciprocalCoefficients n)
noncomputable def fitProjectionWord {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (κ k : ℕ) : List (AdjointStep (Bool×(O⊕I))) :=
  let n := explicitInverseCutoff κ (k+2)
  match (finitePhaseSynthesis (nativeRangeCoefficients n) (2*n) ((1/2:ℚ)^(k+2))).value with
  | none => []
  | some data => fullComputedPhaseWord (rangeProjector (fitRight (O:=O) (I:=I)))
      (rangeProjector (fitLeft (O:=O) (I:=I))) data
noncomputable def fitProjectionPrepare {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (U B : Matrix (O⊕I) (O⊕I) ℂ) (κ k : ℕ) :
    Matrix (Bool×(O⊕I)) (Bool×(O⊕I)) ℂ :=
  evaluate (parallelOracle U) (fitProjectionWord (O:=O) (I:=I) κ k) *
    TensorGate (1 : Matrix Bool Bool ℂ) B
def fitOutputEvent (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Finset (Bool×(O⊕I)) := Finset.univ.filter (fun h => h.1=false ∧ ∃ o : O,h.2=Sum.inl o)
end Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat
namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat
open scoped Classical BigOperators Matrix.Norms.L2Operator

def DataFitActualQualityRestricted : Prop :=
∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  (A : Matrix O I ℂ) (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O) (κ k M : ℕ),
  ProjectedUnitaryEncoding A U fitLeft fitRight → B∈Matrix.unitaryGroup (O⊕I) ℂ →
  B*ᵥKet j=fitLeft*ᵥb → Normalized b → 0 < κ →
  (∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  ∀ hM : 2≤M, ∃ hP : fitProjectionPrepare U B κ k∈Matrix.unitaryGroup (Bool×(O⊕I)) ℂ,
  ∑ z∈Finset.univ.filter (fun z : Fin M =>
    |(1-aeEstimate M z)-‖stateVector (A*ᵥleastSquaresVector A b-b)‖^2|≤
      Real.pi/(M:ℝ)+Real.pi^2/(M:ℝ)^2+(1/2:ℝ)^k),
    (aeLaw M (fitProjectionPrepare U B κ k) (false,j) (fitOutputEvent O I) hP hM).prob z≥8/Real.pi^2
end Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
