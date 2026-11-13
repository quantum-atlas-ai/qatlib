/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat
import Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection

/-!
# Restricted concise fitting from sampled coordinates

This module proves `dataFitConciseSelectionRestricted` by combining computed parameter
preparation, histogram selection bounds, selected-fit residual estimates, and amplitude
estimation. The strengthened specification includes the prepared solution state and its
properties as conclusions, along with the conditional selected-fit preparation and exact query
ledgers, in the setting of [WiebeBraunLloyd2012].

It also records `DataFitConciseSelectionLegacy` and proves its vacuous realization using the
zero vector: the legacy implication makes preparation and solution-state properties premises of
the downstream guarantees.

## Main statements

* `conciseFit_zero_not_solution_state`: exclusion of the zero vector as a solution state.
* `dataFitConciseSelectionRestricted_vacuous`: the legacy implication is satisfied by a
  zero-vector choice.
* `dataFitConciseSelectionRestricted`: the strengthened preparation, selection, and fitting
  guarantees.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
-/

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012
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

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The legacy concise-selection specification whose downstream guarantees are conditional on
preparation and solution-state properties of an existentially chosen vector. This
implication permits choosing a vector that fails those properties. -/
def DataFitConciseSelectionLegacy : Prop :=
∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  (A : Matrix O I ℂ) (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O)
  (U_S B_S : Finset I → Matrix (O⊕I) (O⊕I) ℂ) (j_S : Finset I → O⊕I)
  (κ k κ_S M_ae R : ℕ) (μ : ℝ),
  ProjectedUnitaryEncoding A U fitLeft fitRight →
  B∈Matrix.unitaryGroup (O⊕I) ℂ → B*ᵥKet j = fitLeft*ᵥb → Normalized b → 0<κ →
  (∀ i : Fin (Fintype.card I),0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  (∀ S : Finset I,
    ProjectedUnitaryEncoding (Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.selectedDesignMatrix A S) (U_S S) fitLeft fitRight ∧
    B_S S ∈ Matrix.unitaryGroup (O⊕I) ℂ ∧
    B_S S*ᵥKet (j_S S)=fitLeft*ᵥb ∧
    (∀ i : Fin (Fintype.card I),0 < matrixSingularValues (Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.selectedDesignMatrix A S) i →
      (κ_S:ℝ)⁻¹ ≤ matrixSingularValues (Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.selectedDesignMatrix A S) i)) →
  (hμ : 0<μ) → (hμ1 : μ≤1) → (hM_ae : 2≤M_ae) →
  let cs := finiteInverseWord fitLeft fitRight κ k
  let W := evaluate (parallelOracle U) cs
  let tau := leastSquaresOverlap A b
  ((1/2:ℝ)^k < 2*tau → ∃ phi : QState I,
    postselectionOutput W (coordinatePhaseFrame fitRight) (coordinatePhaseFrame fitLeft) b = some phi ∧
    IsLeastSquaresSolutionState A b phi ((1/2:ℝ)^k/tau) →
    (∃ hφ : Normalized phi,
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.histogramSampleLaw phi hφ R)
        (fun l => Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.missedSelectionMass phi l.toFinset ≤ μ)).toReal
        ≥ 1-(Fintype.card I:ℝ)/((R+1)*μ)) ∧
    (∀ (l : List I), Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.missedSelectionMass phi l.toFinset ≤ μ →
      let S := l.toFinset
      let A_S :=
          Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.selectedDesignMatrix A S
      let P := fitProjectionPrepare (U_S S) (B_S S) κ_S k
      let eta := (1/2:ℝ)^k/tau
      1-tau^2 ≤ ‖stateVector (A_S*ᵥleastSquaresVector A_S b-b)‖^2 ∧
      ‖stateVector (A_S*ᵥleastSquaresVector A_S b-b)‖^2 ≤
        (Real.sqrt (1-tau^2)+‖stateVector (leastSquaresVector A b)‖*
          Real.sqrt (2*μ+2*eta^2))^2 ∧
      ‖stateVector (Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.coordinateTail S (leastSquaresVector A b))‖^2 ≤
        ‖stateVector (leastSquaresVector A b)‖^2*(2*μ+2*eta^2) ∧
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

/-- The zero vector cannot be a least-squares solution state, for any design matrix, target, or
error parameter. -/
theorem conciseFit_zero_not_solution_state {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (η : ℝ) :
    ¬ IsLeastSquaresSolutionState A b (0 : QState I) η := by
  rintro ⟨x, _hx, _hx0, hzero, _herr⟩
  simp [Normalized] at hzero

/-- The inverse of the real cast of the natural number zero is a lower bound for every positive
singular value. -/
theorem conciseFit_zero_kappa_gap {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) :
    ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ((0 : ℕ) : ℝ)⁻¹ ≤ matrixSingularValues A i := by
  intro i hi
  simpa using! hi.le

/-- The legacy concise-selection specification holds by choosing the zero vector, for which the
conditional solution-state premise is false. -/
theorem dataFitConciseSelectionRestricted_vacuous : DataFitConciseSelectionLegacy := by
  intro O I _ _ _ _ A U B j b U_S B_S j_S κ k κ_S M_ae R μ
    _henc _hB _hprep _hb _hκ _hgap _hsub _hμ _hμ1 _hM
  (try dsimp only)
  intro _htau
  refine ⟨0, ?_⟩
  rintro ⟨_hout, hstate⟩
  exact (conciseFit_zero_not_solution_state A b _ hstate).elim

/-- The strengthened concise-selection specification holds, combining actual parameter-state
preparation, histogram selection, selected-fit residual and tail bounds, conditional
selected-parameter preparation, fit-quality estimation, and query counts. The fitting
context is [WiebeBraunLloyd2012]. -/
theorem dataFitConciseSelectionRestricted : DataFitConciseSelectionRestricted := by
  intro O I _ _ _ _ A U B j b U_S B_S j_S κ k κ_S M_ae R μ
    henc _hB _hprep hb hκ hκS hgap hsub hμ _hμ1 hM
  (try dsimp only)
  have hpar := computed_data_fit_actual_parameter O I A U b κ k henc hb hκ hgap
  have hledger := (data_fit_actual_expanded_ae_access_ledger O I κ_S k M_ae hκS hM).2.2
  intro htau
  obtain ⟨phi, hout, hstate⟩ := hpar.1 htau
  have hstatecopy := hstate
  obtain ⟨x, hx, _hx0, hphi, herr⟩ := hstatecopy
  have hcanon := leastSquares_minimum_residual_and_norm A b
  have hxcanon : x = leastSquaresVector A b :=
    hcanon.2 x hx (le_antisymm (hx.2 _ hcanon.1.1) (hcanon.1.2 x hx.1))
  subst x
  refine ⟨phi, hout, hstate, ?_, ?_, hpar.2, hledger⟩
  · refine ⟨hphi, ?_⟩
    exact Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.conciseFit_histogram_markov phi hphi R μ hμ
  · intro l hmiss
    let S := l.toFinset
    let AS :=
        Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.selectedDesignMatrix A S
    let eta := (1/2:ℝ)^k / leastSquaresOverlap A b
    have htail := Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.conciseFit_direction_tail_bound A b S phi eta μ
      hphi hμ.le herr hmiss
    have hA : ‖A‖ ≤ 1 := by
      rw [← henc.encoded]
      exact (compress_norm_le henc.left_isometry henc.right_isometry U).trans
        (unitary_norm_le_one henc.unitary)
    have hres :=
        Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.conciseFit_selected_residual_bounds A b S hb hA
    have hbnd : 0 ≤ 2*μ+2*eta^2 := by positivity
    have ht : ‖stateVector (Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection.coordinateTail S (leastSquaresVector A b))‖ ≤
        ‖stateVector (leastSquaresVector A b)‖ * Real.sqrt (2*μ+2*eta^2) := by
      apply (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt hbnd]
      exact htail
    have hupper := hres.2.trans (pow_le_pow_left₀
      (add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (add_le_add (le_refl (Real.sqrt (1-leastSquaresOverlap A b^2))) ht) 2)
    have hs := hsub S
    have hparS := computed_data_fit_actual_parameter O I AS (U_S S) b κ_S k
      hs.1 hb hκS hs.2.2.2
    have hquality := computed_data_fit_actual_quality O I AS (U_S S) (B_S S)
      (j_S S) b κ_S k M_ae hs.1 hs.2.1 hs.2.2.1 hb hκS hs.2.2.2 hM
    exact ⟨hres.1, hupper, htail, hparS, hquality⟩

end Qatlib.Concepts.LinearLearning.ConcisePipeline
