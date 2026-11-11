/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeConsumers
import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection

/-!
# Specification of restricted concise fitting

This module exports the coordinate-selection and histogram-sampling definitions used by
`DataFitConciseSelectionRestricted`. The proposition combines actual postselected solution-state
preparation with missed-mass probability bounds, selected-fit residual and coefficient-tail
estimates, conditional parameter preparation for the selected design, and amplitude-estimation
guarantees.

The specification retains explicit positive condition bounds and query ledgers for both full and
selected designs, supporting the concise data-fitting task of [WiebeBraunLloyd2012].

## Main definitions

* `selectedDesignMatrix` and `coordinateTail`: selected columns and omitted coefficients.
* `histogramSampleLaw`: repeated sampling from the solution state's Born distribution.
* `DataFitConciseSelectionRestricted`: combined preparation, selection, fitting, and resource
  guarantees.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- Alias for the design matrix with all columns outside the selected finite set replaced by
zero. -/
noncomputable abbrev selectedDesignMatrix :=
    @Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.selectedDesignMatrix
/-- Alias for the vector of coordinates outside the selected finite set. -/
abbrev coordinateTail :=
    @Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.coordinateTail
/-- Alias for the total Born weight outside the selected finite set. -/
noncomputable abbrev missedSelectionMass :=
    @Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.missedSelectionMass
/-- Alias for one coordinate sample from a normalized state's Born distribution. -/
noncomputable abbrev histogramTrial :=
    @Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.histogramTrial
/-- Alias for the law of a list of independent Born-distributed coordinate samples. -/
noncomputable abbrev histogramSampleLaw :=
    @Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.histogramSampleLaw

end Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The restricted concise-fitting specification combining approximate parameter-state
preparation, histogram selection probability, selected-fit residual and tail bounds,
conditional selected-parameter preparation, residual estimation, and exact query ledgers. It
assumes projected-unitary encodings and positive condition bounds for the full and selected
designs. -/
def DataFitConciseSelectionRestricted : Prop :=
∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  (A : Matrix O I ℂ) (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O)
  (U_S B_S : Finset I → Matrix (O⊕I) (O⊕I) ℂ) (j_S : Finset I → O⊕I)
  (κ k κ_S M_ae R : ℕ) (μ : ℝ),
  ProjectedUnitaryEncoding A U fitLeft fitRight →
  B∈Matrix.unitaryGroup (O⊕I) ℂ → B*ᵥKet j = fitLeft*ᵥb → Normalized b → 0<κ → 0<κ_S →
  (∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  (∀ S : Finset I,
    ProjectedUnitaryEncoding (selectedDesignMatrix A S) (U_S S) fitLeft fitRight ∧
    B_S S ∈ Matrix.unitaryGroup (O⊕I) ℂ ∧
    B_S S*ᵥKet (j_S S)=fitLeft*ᵥb ∧
    (∀ i : Fin (Fintype.card I),0 < matrixSingularValues (selectedDesignMatrix A S) i →
      (κ_S:ℝ)⁻¹ ≤ matrixSingularValues (selectedDesignMatrix A S) i)) →
  (hμ : 0<μ) → (hμ1 : μ≤1) → (hM_ae : 2≤M_ae) →
  let cs := finiteInverseWord fitLeft fitRight κ k
  let W := evaluate (parallelOracle U) cs
  let tau := leastSquaresOverlap A b
  ((1/2:ℝ)^k < 2*tau → ∃ phi : QState I,
    postselectionOutput W (coordinatePhaseFrame fitRight) (coordinatePhaseFrame fitLeft) b = some phi ∧
    IsLeastSquaresSolutionState A b phi ((1/2:ℝ)^k/tau) ∧
    (∃ hφ : Normalized phi,
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw phi hφ R)
        (fun l => missedSelectionMass phi l.toFinset ≤ μ)).toReal
        ≥ 1-(Fintype.card I:ℝ)/((R+1)*μ)) ∧
    (∀ (l : List I), missedSelectionMass phi l.toFinset ≤ μ →
      let S := l.toFinset
      let A_S := selectedDesignMatrix A S
      let P := fitProjectionPrepare (U_S S) (B_S S) κ_S k
      let eta := (1/2:ℝ)^k/tau
      1-tau^2 ≤ ‖stateVector (A_S*ᵥleastSquaresVector A_S b-b)‖^2 ∧
      ‖stateVector (A_S*ᵥleastSquaresVector A_S b-b)‖^2 ≤
        (Real.sqrt (1-tau^2)+‖stateVector (leastSquaresVector A b)‖*
          Real.sqrt (2*μ+2*eta^2))^2 ∧
      ‖stateVector (coordinateTail S (leastSquaresVector A b))‖^2 ≤
        ‖stateVector (leastSquaresVector A b)‖^2*(2*μ+2*eta^2) ∧
      (((1/2:ℝ)^k < 2*leastSquaresOverlap A_S b → ∃ phi_S : QState I,
        postselectionOutput
          (evaluate (parallelOracle (U_S S)) (finiteInverseWord fitLeft fitRight κ_S k))
          (coordinatePhaseFrame fitRight) (coordinatePhaseFrame fitLeft) b = some phi_S ∧
        IsLeastSquaresSolutionState A_S b phi_S
          ((1/2:ℝ)^k/leastSquaresOverlap A_S b)) ∧
        adjointQueryCount (finiteInverseWord
          (fitLeft : Matrix (O⊕I) O ℂ) (fitRight : Matrix (O⊕I) I ℂ) κ_S k) =
          2*explicitInverseCutoff κ_S (k+2)-1) ∧
      ∃ hP : P ∈ Matrix.unitaryGroup (Bool×(O⊕I)) ℂ,
        ∑ z∈Finset.univ.filter (fun z : Fin M_ae =>
          |(1-aeEstimate M_ae z)-‖stateVector (A_S*ᵥleastSquaresVector A_S b-b)‖^2| ≤
            Real.pi/(M_ae:ℝ)+Real.pi^2/(M_ae:ℝ)^2+(1/2:ℝ)^k),
          (aeLaw M_ae P (false,j_S S)
            (fitOutputEvent O I) hP hM_ae).prob z ≥ 8/Real.pi^2) ∧
    adjointQueryCount cs = 2*explicitInverseCutoff κ (k+2)-1 ∧
    aeInputAccesses (aeAccessWord (I:=Bool×(O⊕I)) M_ae)*
      adjointQueryCount (fitProjectionWord (O:=O) (I:=I) κ_S k) =
        (2*M_ae-1)*(2*explicitInverseCutoff κ_S (k+2)))

end Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012
