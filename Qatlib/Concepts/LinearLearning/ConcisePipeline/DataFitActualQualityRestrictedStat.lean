/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# Specification of restricted fit-quality estimation

This module defines direct-sum coordinate embeddings, a computed range-projection phase word,
its preparation matrix, and the output event used to read its amplitude. The proposition
`DataFitActualQualityRestricted` states unitarity and a probability bound for estimating the
squared least-squares residual, with explicit phase-approximation and amplitude-estimation
errors.

The fitting task follows the setting of [WiebeBraunLloyd2012], and the readout uses
amplitude-estimation constructions associated with [BrassardEtAl2002].

## Main definitions

* `fitProjectionPrepare`: the evaluated range-projection word composed with target preparation.
* `fitOutputEvent`: the output-summand event in the Boolean-extended register.
* `DataFitActualQualityRestricted`: the fit-quality estimation specification.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

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
/-- The canonical coordinate embedding of the output space into the left summand of `O ⊕ I`. -/
noncomputable def fitLeft {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Matrix (O⊕I) O ℂ := fun h o => if h=Sum.inl o then 1 else 0
/-- The canonical coordinate embedding of the parameter space into the right summand of `O ⊕ I`. -/
noncomputable def fitRight {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Matrix (O⊕I) I ℂ := fun h i => if h=Sum.inr i then 1 else 0
/-- The rational coefficients obtained by multiplying the native reciprocal polynomial by the
polynomial with coefficients `[0, 1]`. -/
def nativeRangeCoefficients (n : ℕ) : List ℚ := ratMulList [0,1] (nativeReciprocalCoefficients n)
/-- The computed phase word for the range polynomial at the specified inverse cutoff and dyadic
tolerance, using the parameter and output range projectors; it is empty if phase synthesis
returns no data. -/
noncomputable def fitProjectionWord {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (κ k : ℕ) : List (AdjointStep (Bool×(O⊕I))) :=
  let n := explicitInverseCutoff κ (k+2)
  match (finitePhaseSynthesis (nativeRangeCoefficients n) (2*n) ((1/2:ℚ)^(k+2))).value with
  | none => []
  | some data => fullComputedPhaseWord (rangeProjector (fitRight (O:=O) (I:=I)))
      (rangeProjector (fitLeft (O:=O) (I:=I))) data
/-- The joint-register preparation matrix obtained by evaluating the computed range-projection
word and composing it with the supplied data-preparation matrix on the system register. -/
noncomputable def fitProjectionPrepare {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (U B : Matrix (O⊕I) (O⊕I) ℂ) (κ k : ℕ) :
    Matrix (Bool×(O⊕I)) (Bool×(O⊕I)) ℂ :=
  evaluate (parallelOracle U) (fitProjectionWord (O:=O) (I:=I) κ k) *
    TensorGate (1 : Matrix Bool Bool ℂ) B
/-- The joint basis event with Boolean coordinate `false` and system coordinate in the output
summand. -/
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

/-- The restricted fit-quality specification for a projected-unitary encoding and a unitary
preparation of a normalized target under a nonzero-singular-value lower bound. It requires a
unitary computed projection preparation and residual estimation within `π / M + π ^ 2 / M ^
2 + (1 / 2) ^ k` with probability at least `8 / π ^ 2` for `M ≥ 2`. -/
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
