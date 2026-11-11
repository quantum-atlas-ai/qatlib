/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# Specification of restricted data-fitting parameter preparation

This module defines the coordinate embeddings `fitLeft` and `fitRight` and the finite
phase-synthesis components `fitProjectionWord` and `fitProjectionPrepare`. The proposition
`DataFitActualParameterRestricted` specifies postselected approximation of the least-squares
direction and the exact finite-inverse query count under a projected-unitary encoding and a
nonzero-singular-value lower bound.

The data-fitting context is [WiebeBraunLloyd2012]; the computed polynomial framework is related
to singular-value transformation in [GilyenSuLowWiebe2019].

## Main definitions

* `fitLeft` and `fitRight`: coordinate embeddings into the direct-sum system space.
* `fitProjectionWord`: a range-polynomial phase word from finite phase synthesis.
* `DataFitActualParameterRestricted`: the parameter-state approximation and query-count
  specification.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.LinearSystems
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
namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat
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
end Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat
namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The restricted parameter-preparation specification for projected-unitary encodings with
positive condition bound and a lower bound on nonzero singular values. It requires
approximate postselected least-squares states when the dyadic error is below twice the
overlap, and the exact finite-inverse adjoint-query count. -/
def DataFitActualParameterRestricted : Prop :=
∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  (A : Matrix O I ℂ) (U : Matrix (O⊕I) (O⊕I) ℂ) (b : QState O) (κ k : ℕ),
  ProjectedUnitaryEncoding A U fitLeft fitRight → Normalized b → 0 < κ →
  (∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  let cs := finiteInverseWord fitLeft fitRight κ k
  let W := evaluate (parallelOracle U) cs
  let tau := leastSquaresOverlap A b
  ((1/2:ℝ)^k < 2*tau → ∃ phi : QState I,
    postselectionOutput W (coordinatePhaseFrame fitRight) (coordinatePhaseFrame fitLeft) b=some phi ∧
    IsLeastSquaresSolutionState A b phi ((1/2:ℝ)^k/tau)) ∧
  adjointQueryCount cs=2*explicitInverseCutoff κ (k+2)-1
end Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012
