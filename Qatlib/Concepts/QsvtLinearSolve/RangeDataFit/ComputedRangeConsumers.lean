/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeProjection

/-!
# Computed data-fitting quality and access costs

This module turns computed range projection and inverse words into least-squares and
ridge-regression guarantees. It relates measured projection probabilities to residual objectives
and expands amplitude-estimation accesses into underlying oracle counts, using the QSVT
framework of [GilyenSuLowWiebe2019].

## Main statements

* `computed_data_fit_actual_quality`: A probability guarantee for estimating the least-squares
  residual.
* `computed_data_fit_actual_parameter`: Conditional preparation of a least-squares solution
  state.
* `ridge_fit_actual_quality_and_access`: Ridge-objective estimation together with exact expanded
  access counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- For normalized input `b`, the squared least-squares residual equals one minus the squared
least-squares overlap. -/
theorem fit_minimum_residual_quality {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (hb : Normalized b) :
    ‖stateVector (A*ᵥleastSquaresVector A b-b)‖^2 = 1-(leastSquaresOverlap A b)^2 := by
  have hh := (leastSquares_overlap_and_zero A b).2.2.2
  rw [(normalized_iff_stateVector_norm b).mp hb, one_pow] at hh
  linarith

/-- Under the encoding, preparation, and singular-value gap assumptions, amplitude estimation
approximates the squared least-squares residual within `π / M + π² / M² + (1/2)^k` with
probability at least `8 / π²`. -/
theorem computed_data_fit_actual_quality
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O) (κ k M : ℕ)
    (henc : ProjectedUnitaryEncoding A U fitLeft fitRight) (hB : B∈Matrix.unitaryGroup (O⊕I) ℂ)
    (hprep : B*ᵥKet j=fitLeft*ᵥb) (hb : Normalized b) (hκ : 0<κ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i)
    (hM : 2≤M) : ∃ hP : fitProjectionPrepare U B κ k∈Matrix.unitaryGroup (Bool×(O⊕I)) ℂ,
    ∑ z∈Finset.univ.filter (fun z : Fin M =>
      |(1-aeEstimate M z)-‖stateVector (A*ᵥleastSquaresVector A b-b)‖^2|≤
        Real.pi/(M:ℝ)+Real.pi^2/(M:ℝ)^2+(1/2:ℝ)^k),
      (aeLaw M (fitProjectionPrepare U B κ k) (false,j) (fitOutputEvent O I) hP hM).prob z≥8/Real.pi^2 := by
  have hresult := computed_range_actual_word_and_mass O I A U B j b κ k henc hB hprep hb hκ hgap
  let P := fitProjectionPrepare U B κ k
  let a := MeasureProb (preparedAAState P (false,j)) (fitOutputEvent O I)
  have hP : P∈Matrix.unitaryGroup (Bool×(O⊕I)) ℂ := hresult.1
  have hm : |a-(leastSquaresOverlap A b)^2|≤(1/2:ℝ)^k := hresult.2.2.2.2
  have ha0 : 0≤a := measureProb_nonneg _ _
  have ha1 : a≤1 := measureProb_le_one (normalized_applyGate hP (normalized_ket _)) _
  have hsqrt : Real.sqrt (a*(1-a))≤1/2 := by
    have hh := Real.sq_sqrt (mul_nonneg ha0 (by linarith : 0≤1-a))
    nlinarith [Real.sqrt_nonneg (a*(1-a)), sq_nonneg (a-1/2)]
  have hbudget : 2*Real.pi*Real.sqrt (a*(1-a))/(M:ℝ)≤Real.pi/(M:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    nlinarith [Real.pi_pos]
  have hgood := (prepared_ae_bhmt_error_and_endpoints M hM P (false,j) (fitOutputEvent O I) hP).1
  refine ⟨hP, hgood.trans ?_⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    obtain ⟨_, hz⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [fit_minimum_residual_quality A b hb]
    have htri := abs_sub_le (aeEstimate M z) a ((leastSquaresOverlap A b)^2)
    have heq : |(1-aeEstimate M z)-(1-(leastSquaresOverlap A b)^2)| =
        |aeEstimate M z-(leastSquaresOverlap A b)^2| := by
      rw [show (1-aeEstimate M z)-(1-(leastSquaresOverlap A b)^2) =
        -(aeEstimate M z-(leastSquaresOverlap A b)^2) by ring, abs_neg]
    rw [heq]
    change |aeEstimate M z-a|≤2*Real.pi*Real.sqrt (a*(1-a))/(M:ℝ)+Real.pi^2/(M:ℝ)^2 at hz
    linarith
  · intro z _ _
    exact (aeLaw M P (false,j) (fitOutputEvent O I) hP hM).nonneg z

/-- The computed inverse word has the stated exact query count and, when its accuracy is smaller
than twice the overlap, produces a least-squares solution state with error `(1/2)^k / tau`. -/
theorem computed_data_fit_actual_parameter
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (U : Matrix (O⊕I) (O⊕I) ℂ) (b : QState O) (κ k : ℕ)
    (henc : ProjectedUnitaryEncoding A U fitLeft fitRight) (hb : Normalized b) (hκ : 0<κ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → (κ:ℝ)⁻¹≤ matrixSingularValues A i) :
    let cs := finiteInverseWord fitLeft fitRight κ k
    let W := evaluate (parallelOracle U) cs
    let tau := leastSquaresOverlap A b
    (((1/2:ℝ)^k < 2*tau → ∃ phi : QState I,
      postselectionOutput W (coordinatePhaseFrame fitRight) (coordinatePhaseFrame fitLeft) b=some phi ∧
      IsLeastSquaresSolutionState A b phi ((1/2:ℝ)^k/tau)) ∧
      adjointQueryCount cs=2*explicitInverseCutoff κ (k+2)-1) := by
  have hh :=
      computed_inverse_actual_least_squares_and_zero
      (O⊕I) I O A U fitLeft fitRight κ k b henc hκ hb hgap
  have hc :=
      computed_full_inverse_actual_encoding_and_cost (O⊕I) I O A U fitLeft fitRight κ k henc hκ hgap
  exact ⟨fun ht => (hh.1 ht).2, hc.2.2.2.1⟩

/-- Least squares on the ridge-augmented system minimizes the ridge objective for nonnegative
`lam`. For normalized input, the minimum objective equals one minus the squared
augmented-system overlap. -/
theorem data_fit_ridge_objective_and_quality
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (b : QState O) (lam : ℝ) (hlam : 0≤lam) (hb : Normalized b) :
    let F := ridgeAugmentedMatrix A lam
    let y := ridgeAugmentedInput (I:=I) b
    let x := leastSquaresVector F y
    (∀ z : QState I, ‖stateVector (A*ᵥx-b)‖^2+lam*‖stateVector x‖^2≤
      ‖stateVector (A*ᵥz-b)‖^2+lam*‖stateVector z‖^2) ∧
    ‖stateVector (A*ᵥx-b)‖^2+lam*‖stateVector x‖^2=1-(leastSquaresOverlap F y)^2 := by
  (try dsimp only)
  have hy : Normalized (ridgeAugmentedInput (I:=I) b) := by
    simpa [Normalized, ridgeAugmentedInput, Fintype.sum_sum_type] using! hb
  constructor
  · intro z
    have hh := (leastSquares_minimum_residual_and_norm (ridgeAugmentedMatrix A lam)
      (ridgeAugmentedInput b)).1.1 z
    have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
    rwa [ridge_augmented_residual A b lam _ hlam, ridge_augmented_residual A b lam z hlam] at hsq
  · rw [← ridge_augmented_residual A b lam _ hlam]
    exact fit_minimum_residual_quality _ _ hy

/-- The amplitude-estimation input access count is the sum of its forward and backward accesses. -/
private theorem fit_ae_input_split {R : Type} (w : List (AEAccessStep R)) :
    aeInputAccesses w=aeForwardAccesses w+aeBackwardAccesses w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp [aeInputAccesses, aeForwardAccesses, aeBackwardAccesses] at * <;> omega

/-- For `M ≥ 2`, amplitude estimation uses `M` forward and `M - 1` backward accesses, yielding
`(2 * M - 1) * (2 * explicitInverseCutoff κ (k + 2))` expanded projection-word queries. -/
theorem data_fit_actual_expanded_ae_access_ledger
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (κ k M : ℕ) (_hκ : 0 < κ) (hM : 2≤M) :
    aeForwardAccesses (aeAccessWord (I:=Bool×(O⊕I)) M)=M ∧
    aeBackwardAccesses (aeAccessWord (I:=Bool×(O⊕I)) M)=M-1 ∧
    aeInputAccesses (aeAccessWord (I:=Bool×(O⊕I)) M)*
      adjointQueryCount (fitProjectionWord (O:=O) (I:=I) κ k)=
        (2*M-1)*(2*explicitInverseCutoff κ (k+2)) := by
  have hc := prepared_ae_separate_access_counts (I:=Bool×(O⊕I)) M (by omega)
  have hn := (nativeRangeCoefficients_admissible (explicitInverseCutoff κ (k+2)))
  obtain ⟨data, hdata, hlen, _, _, _, _, _⟩ := finite_rational_phase_synthesis_terminates
    (nativeRangeCoefficients (explicitInverseCutoff κ (k+2))) (2*explicitInverseCutoff κ (k+2))
    ((1/2:ℚ)^(k+2)) (by positivity) hn.1 hn.2 (nativeRangeCoefficients_bounded _)
  have hq : adjointQueryCount (fitProjectionWord (O:=O) (I:=I) κ k)=2*explicitInverseCutoff κ (k+2) := by
    unfold fitProjectionWord
    (try dsimp only)
    rw [hdata]
    simp only [fullComputedPhaseWord, adjointQueryCount_append, adjointQueryCount,
      computedPhaseWord, (counts_compileRealPartQSVT _ _ _ _).1, List.length_map, hlen]
    omega
  refine ⟨hc.1, hc.2.1, ?_⟩
  rw [fit_ae_input_split, hc.1, hc.2.1, hq]
  congr 1
  omega

/-- Under the augmented encoding, preparation, and gap assumptions, the ridge objective is
estimated within `π / M + π² / M² + (1/2)^k` with probability at least `8 / π²`. The theorem
also records exact forward, backward, and expanded oracle access counts. -/
theorem ridge_fit_actual_quality_and_access
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (b : QState O) (lam : ℝ)
    (U B : Matrix ((O⊕I)⊕I) ((O⊕I)⊕I) ℂ) (j : (O⊕I)⊕I) (κ k M : ℕ)
    (hlam : 0≤lam) (hb : Normalized b)
    (henc : ProjectedUnitaryEncoding (ridgeAugmentedMatrix A lam) U fitLeft fitRight)
    (hB : B∈Matrix.unitaryGroup ((O⊕I)⊕I) ℂ)
    (hprep : B*ᵥKet j=fitLeft*ᵥridgeAugmentedInput (I:=I) b) (hκ : 0<κ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues (ridgeAugmentedMatrix A lam) i →
      (κ:ℝ)⁻¹≤ matrixSingularValues (ridgeAugmentedMatrix A lam) i) (hM : 2≤M) :
    let F := ridgeAugmentedMatrix A lam
    let y := ridgeAugmentedInput (I:=I) b
    let x := leastSquaresVector F y
    ∃ hP : fitProjectionPrepare U B κ k∈Matrix.unitaryGroup (Bool×((O⊕I)⊕I)) ℂ,
      (∑ z∈Finset.univ.filter (fun z : Fin M =>
        |(1-aeEstimate M z)-(‖stateVector (A*ᵥx-b)‖^2+lam*‖stateVector x‖^2)|≤
          Real.pi/(M:ℝ)+Real.pi^2/(M:ℝ)^2+(1/2:ℝ)^k),
        (aeLaw M (fitProjectionPrepare U B κ k) (false,j) (fitOutputEvent (O⊕I) I) hP hM).prob z)≥8/Real.pi^2 ∧
      aeForwardAccesses (aeAccessWord (I:=Bool×((O⊕I)⊕I)) M)=M ∧
      aeBackwardAccesses (aeAccessWord (I:=Bool×((O⊕I)⊕I)) M)=M-1 ∧
      aeInputAccesses (aeAccessWord (I:=Bool×((O⊕I)⊕I)) M)*
        adjointQueryCount (fitProjectionWord (O:=O⊕I) (I:=I) κ k)=
          (2*M-1)*(2*explicitInverseCutoff κ (k+2)) := by
  (try dsimp only)
  have hy : Normalized (ridgeAugmentedInput (I:=I) b) := by
    simpa [Normalized, ridgeAugmentedInput, Fintype.sum_sum_type] using! hb
  obtain ⟨hP,hquality⟩ := computed_data_fit_actual_quality (O⊕I) I (ridgeAugmentedMatrix A lam)
    U B j (ridgeAugmentedInput b) κ k M henc hB hprep hy hκ hgap hM
  rw [ridge_augmented_residual A b lam _ hlam] at hquality
  exact ⟨hP,hquality,data_fit_actual_expanded_ae_access_ledger (O⊕I) I κ k M hκ hM⟩

end Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
