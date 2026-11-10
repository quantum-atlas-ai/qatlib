/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.FixedPointDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix Qatlib
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

theorem projector_flag_norm_le_one (S : Finset (Fin 3)) : ‖Projector S‖ ≤ 1 := by
  rw [show Projector S = Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) from rfl,
    Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  split_ifs <;> simp

theorem projector_flag_contract (S : Finset (Fin 3)) (w : QState (Fin 3)) :
    ‖toEuclidean_fromVec (Projector S *ᵥ w)‖ ≤ ‖toEuclidean_fromVec w‖ := by
  have h := Matrix.l2_opNorm_mulVec (Projector S) (toEuclidean_fromVec w)
  have hp : ‖Projector S‖ ≤ 1 := projector_flag_norm_le_one S
  calc ‖toEuclidean_fromVec (Projector S *ᵥ w)‖ ≤ ‖Projector S‖ * ‖toEuclidean_fromVec w‖ := h
    _ ≤ 1 * ‖toEuclidean_fromVec w‖ := by
        exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ‖toEuclidean_fromVec w‖ := by ring

theorem collapse_contract (S : Finset (Fin 3)) (w : QState (Fin 3)) :
    ‖toEuclidean_fromVec (Collapse w S)‖ ≤ ‖toEuclidean_fromVec w‖ := by
  have hsq : ‖toEuclidean_fromVec (Collapse w S)‖ ^ 2 ≤ ‖toEuclidean_fromVec w‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    calc (∑ i, ‖Collapse w S i‖ ^ 2) = MeasureProb w S := sum_normSq_collapse w S
      _ ≤ MeasureProb w Finset.univ := measureProb_mono w (Finset.subset_univ S)
      _ = ∑ i, ‖w i‖ ^ 2 := by simp [MeasureProb, BornProb]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem ket_flag_norm (i : Fin 3) : ‖toEuclidean_fromVec (Ket i)‖ = 1 :=
  (normalized_iff_norm_toEuclidean_fromVec (Ket i)).mp (normalized_ket i)

theorem collapse_sub (S : Finset (Fin 3)) (u v : QState (Fin 3)) :
    Collapse u S - Collapse v S = Collapse (u - v) S := by
  funext i
  simp only [Pi.sub_apply, collapse_apply]
  by_cases hi : i ∈ S <;> simp [hi]

theorem clause20_actual_well_mass (d θ : ℝ) (hd : 0 < d) :
    sinEnvelopeActualWellMass d θ hd = sinEnvelopeIdealWellMass d θ := by
  unfold sinEnvelopeActualWellMass sinEnvelopeIdealWellMass instrumentProb
  unfold sinEnvelopeFilterInstrument
  rw [basis_event_pure_branch, trace_outerProduct]
  have hcollapse :
      ProjectiveBranch (Projector sinEnvelopeWellEvent) true
          (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3))) =
        Collapse (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))
          sinEnvelopeWellEvent := by
    unfold ProjectiveBranch Collapse
    simp only [if_true]
  rw [hcollapse, sum_normSq_collapse]
  have hcol : ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)) =
      sinEnvelopeHVector d θ := by
    simp only [ApplyGate]
    exact (sin_envelope_flag_rotation_unitary_and_column d θ hd).2
  rw [hcol]
  have hf : 0 ≤ sinEnvelopeFilterF d θ := (sin_envelope_filter_nonnegative d θ hd).1
  simp only [MeasureProb, sinEnvelopeWellEvent, Finset.sum_singleton, BornProb]
  rw [show (sinEnvelopeHVector d θ) sinEnvelopeWellFlag = (sinEnvelopeFilterF d θ : ℂ) by
    simp [sinEnvelopeHVector, sinEnvelopeWellFlag]]
  rw [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]

theorem clause20_actual_well_output (d θ : ℝ) (hd : 0 < d)
    (hf : 0 < sinEnvelopeFilterF d θ) :
    sinEnvelopeActualWellOutput d θ hd = some (Ket (1 : Fin 3)) := by
  unfold sinEnvelopeActualWellOutput
  have hcol : ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)) =
      sinEnvelopeHVector d θ := by
    simp only [ApplyGate]
    exact (sin_envelope_flag_rotation_unitary_and_column d θ hd).2
  rw [hcol]
  have hbranch : ProjectiveBranch (Projector sinEnvelopeWellEvent) true
        (sinEnvelopeHVector d θ) =
      Collapse (sinEnvelopeHVector d θ) sinEnvelopeWellEvent := by
    unfold ProjectiveBranch Collapse
    simp only [if_true]
  unfold ProjectiveConditionalState
  rw [hbranch]
  have hmass : MeasureProb (Collapse (sinEnvelopeHVector d θ) sinEnvelopeWellEvent)
        Finset.univ = (sinEnvelopeFilterF d θ) ^ 2 := by
    have h3 : MeasureProb (Collapse (sinEnvelopeHVector d θ) sinEnvelopeWellEvent)
          Finset.univ =
        ∑ i, ‖Collapse (sinEnvelopeHVector d θ) sinEnvelopeWellEvent i‖ ^ 2 := by
      simp [MeasureProb, BornProb]
    rw [h3, sum_normSq_collapse]
    have hfn : 0 ≤ sinEnvelopeFilterF d θ := (sin_envelope_filter_nonnegative d θ hd).1
    simp only [MeasureProb, sinEnvelopeWellEvent, Finset.sum_singleton, BornProb]
    rw [show (sinEnvelopeHVector d θ) sinEnvelopeWellFlag = (sinEnvelopeFilterF d θ : ℂ) by
      simp [sinEnvelopeHVector, sinEnvelopeWellFlag]]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfn]
  unfold ConditionalState
  rw [if_pos (by rw [hmass]; positivity)]
  have hcollapse2 (i : Fin 3) :
      Collapse (Collapse (sinEnvelopeHVector d θ) sinEnvelopeWellEvent) Finset.univ i =
        if i ∈ sinEnvelopeWellEvent then (sinEnvelopeHVector d θ) i else 0 := by
    rw [collapse_apply]
    simp only [Finset.mem_univ, if_true]
    rw [collapse_apply]
  have hpost : PostMeasure (Collapse (sinEnvelopeHVector d θ) sinEnvelopeWellEvent)
      Finset.univ = Ket (1 : Fin 3) := by
    funext i
    simp only [PostMeasure]
    rw [hcollapse2 i, hmass]
    by_cases hi : i ∈ sinEnvelopeWellEvent
    · have hi1 : i = sinEnvelopeWellFlag := by
        simpa [sinEnvelopeWellEvent, sinEnvelopeWellFlag] using! hi
      subst hi1
      have hfn : 0 ≤ sinEnvelopeFilterF d θ := (sin_envelope_filter_nonnegative d θ hd).1
      have hsqrt : Real.sqrt (sinEnvelopeFilterF d θ ^ 2) = sinEnvelopeFilterF d θ :=
        Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg hfn)
      have hfne : (sinEnvelopeFilterF d θ : ℂ) ≠ 0 := by simp [hf.ne']
      simp only [hi, if_true]
      rw [show (sinEnvelopeHVector d θ) sinEnvelopeWellFlag = (sinEnvelopeFilterF d θ : ℂ) by
        simp [sinEnvelopeHVector, sinEnvelopeWellFlag]]
      rw [hsqrt]
      rw [inv_mul_cancel₀ hfne]
      simp [Qatlib.Foundations.PureStateMath.Ket, sinEnvelopeWellFlag]
    · have hi1 : i ≠ (1 : Fin 3) := by
        intro hcon
        apply hi
        have h2 : i = sinEnvelopeWellFlag := by simpa [sinEnvelopeWellFlag] using! hcon
        simp [sinEnvelopeWellEvent, h2]
      simp [hi, hi1, Qatlib.Foundations.PureStateMath.Ket]
  rw [hpost]

theorem clause20_ideal_well_measureProb (d θ : ℝ) (hd : 0 < d) :
    MeasureProb (sinEnvelopeFlagRotation d θ *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent
      = (sinEnvelopeFilterF d θ) ^ 2 := by
  rw [(sin_envelope_flag_rotation_unitary_and_column d θ hd).2]
  have hfn : 0 ≤ sinEnvelopeFilterF d θ := (sin_envelope_filter_nonnegative d θ hd).1
  simp only [MeasureProb, sinEnvelopeWellEvent, Finset.sum_singleton, BornProb]
  rw [show (sinEnvelopeHVector d θ) sinEnvelopeWellFlag = (sinEnvelopeFilterF d θ : ℂ) by
    simp [sinEnvelopeHVector, sinEnvelopeWellFlag]]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfn]

theorem clause20_reference_branch_norm (d θ : ℝ) (hd : 0 < d) :
    ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ hd)‖ = sinEnvelopeFilterF d θ := by
  have hsq : ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ hd)‖ ^ 2
      = (sinEnvelopeFilterF d θ) ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq]
    have h1 : (∑ i, ‖Collapse (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))
          sinEnvelopeWellEvent i‖ ^ 2)
        = MeasureProb (sinEnvelopeFlagRotation d θ *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent := by
      have h2 := (sum_normSq_collapse (ApplyGate (sinEnvelopeFlagRotation d θ) (Ket (0 : Fin 3)))
        sinEnvelopeWellEvent)
      rw [h2]
      rfl
    simp only [sinEnvelopeActualWellVector]
    rw [h1, clause20_ideal_well_measureProb d θ hd]
  have hfn : 0 ≤ sinEnvelopeFilterF d θ := (sin_envelope_filter_nonnegative d θ hd).1
  have hpos : 0 ≤ ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ hd)‖ := norm_nonneg _
  have h1 : ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ hd)‖
      ≤ sinEnvelopeFilterF d θ :=
    (sq_le_sq₀ hpos hfn).mp (le_of_eq hsq)
  have h2 : sinEnvelopeFilterF d θ
      ≤ ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ hd)‖ :=
    (sq_le_sq₀ hfn hpos).mp (le_of_eq hsq.symm)
  exact le_antisymm h1 h2

theorem clause20_tight_well_parameters (d θ : ℝ) (hd : 0 < d) :
    sinEnvelopeActualWellMass d (2 * d) hd = 1 / 4 ∧
    sinEnvelopeIdealIllMass d (2 * d) = 0 ∧
    (∀ θ', 2 * d ≤ θ' → sinEnvelopeIdealWellMass d θ' = (d / θ') ^ 2) := by
  have h := sin_envelope_filter_branch_values d hd
  refine ⟨?_, ?_, ?_⟩
  · rw [clause20_actual_well_mass]
    simp only [sinEnvelopeIdealWellMass]
    rw [h.1]
    norm_num
  · simp only [sinEnvelopeIdealIllMass]
    rw [h.2.1]
    norm_num
  · intro θ' hθ'
    simp only [sinEnvelopeIdealWellMass]
    rw [(h.2.2.2.2.2.2.2.2 θ' hθ').1]

theorem clause20_executed_branch_error {d θ : ℝ} (E : SinEnvelopeFilterExecution d θ) :
    ‖toEuclidean_fromVec (E.wellVector - sinEnvelopeActualWellVector d θ E.threshold_pos)‖
      ≤ E.error := by
  have hlin : E.wellVector - sinEnvelopeActualWellVector d θ E.threshold_pos
      = Collapse ((E.rotation - sinEnvelopeFlagRotation d θ) *ᵥ Ket (0 : Fin 3))
          sinEnvelopeWellEvent := by
    funext i
    simp only [SinEnvelopeFilterExecution.wellVector, sinEnvelopeActualWellVector, ApplyGate,
      Pi.sub_apply, collapse_apply]
    by_cases hi : i ∈ sinEnvelopeWellEvent
    · simp only [hi, if_true]
      have hh := congrFun (Matrix.sub_mulVec (E.rotation) (sinEnvelopeFlagRotation d θ)
        (Ket (0 : Fin 3))) i
      simpa only [Pi.sub_apply] using! hh.symm
    · simp [hi]
  rw [hlin]
  calc ‖toEuclidean_fromVec
        (Collapse ((E.rotation - sinEnvelopeFlagRotation d θ) *ᵥ Ket (0 : Fin 3))
          sinEnvelopeWellEvent)‖
      ≤ ‖toEuclidean_fromVec
        ((E.rotation - sinEnvelopeFlagRotation d θ) *ᵥ Ket (0 : Fin 3))‖ :=
        collapse_contract _ _
    _ ≤ ‖E.rotation - sinEnvelopeFlagRotation d θ‖ * ‖toEuclidean_fromVec (Ket (0 : Fin 3))‖ := by
        exact Matrix.l2_opNorm_mulVec (E.rotation - sinEnvelopeFlagRotation d θ)
          (toEuclidean_fromVec (Ket (0 : Fin 3)))
    _ ≤ E.error * 1 := by
        rw [ket_flag_norm]
        exact mul_le_mul_of_nonneg_right E.error_le (by norm_num)
    _ = E.error := by ring

theorem clause20_executed_mass_stability {d θ : ℝ} (E : SinEnvelopeFilterExecution d θ) :
    |E.wellMass - sinEnvelopeIdealWellMass d θ|
      ≤ E.error * (2 * sinEnvelopeFilterF d θ + E.error) := by
  have hsqref : ‖toEuclidean_fromVec
        (sinEnvelopeActualWellVector d θ E.threshold_pos)‖ ^ 2
      = sinEnvelopeIdealWellMass d θ := by
    rw [clause20_reference_branch_norm d θ E.threshold_pos]
    simp only [sinEnvelopeIdealWellMass]
  have hsqexec : ‖toEuclidean_fromVec (E.wellVector)‖ ^ 2 = E.wellMass := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [SinEnvelopeFilterExecution.wellVector]
    have h1 : (∑ i, ‖Collapse (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent i‖ ^ 2)
        = MeasureProb (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent := by
      have h2 := (sum_normSq_collapse (E.rotation *ᵥ Ket (0 : Fin 3)) sinEnvelopeWellEvent)
      rw [h2]
    rw [h1]
    simp only [SinEnvelopeFilterExecution.wellMass]
  have hclose : ‖toEuclidean_fromVec (E.wellVector) -
        toEuclidean_fromVec (sinEnvelopeActualWellVector d θ E.threshold_pos)‖ ≤ E.error := by
    have heq : toEuclidean_fromVec (E.wellVector) -
        toEuclidean_fromVec (sinEnvelopeActualWellVector d θ E.threshold_pos)
        = toEuclidean_fromVec (E.wellVector - sinEnvelopeActualWellVector d θ E.threshold_pos) := by
      simp only [toEuclidean_fromVec, WithLp.toLp_sub]
    rw [heq]
    exact clause20_executed_branch_error E
  have h := Qatlib.Concepts.BlockEncoding.Postselection.norm_sq_error hclose
  rw [hsqexec, hsqref] at h
  rw [clause20_reference_branch_norm d θ E.threshold_pos] at h
  exact h

theorem clause20_executed_output_stability {d θ : ℝ} (E : SinEnvelopeFilterExecution d θ)
    (hgap : E.error < sinEnvelopeFilterF d θ) :
    toEuclidean_fromVec (E.wellVector) ≠ 0 ∧
    ‖NormedSpace.normalize (toEuclidean_fromVec (E.wellVector)) -
        NormedSpace.normalize (toEuclidean_fromVec
          (sinEnvelopeActualWellVector d θ E.threshold_pos))‖
      ≤ 2 * E.error / sinEnvelopeFilterF d θ := by
  have hclose : ‖toEuclidean_fromVec (E.wellVector) -
        toEuclidean_fromVec (sinEnvelopeActualWellVector d θ E.threshold_pos)‖ ≤ E.error := by
    have heq : toEuclidean_fromVec (E.wellVector) -
        toEuclidean_fromVec (sinEnvelopeActualWellVector d θ E.threshold_pos)
        = toEuclidean_fromVec (E.wellVector - sinEnvelopeActualWellVector d θ E.threshold_pos) := by
      simp only [toEuclidean_fromVec, WithLp.toLp_sub]
    rw [heq]
    exact clause20_executed_branch_error E
  have hnorm : ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ E.threshold_pos)‖
      = sinEnvelopeFilterF d θ :=
    clause20_reference_branch_norm d θ E.threshold_pos
  have hgap' : E.error <
      ‖toEuclidean_fromVec (sinEnvelopeActualWellVector d θ E.threshold_pos)‖ := by
    rw [hnorm]
    exact hgap
  obtain ⟨hne, hbound⟩ :=
    Qatlib.Concepts.BlockEncoding.Postselection.normalize_error_of_gap hclose hgap'
  constructor
  · exact hne
  · rw [hnorm] at hbound
    exact hbound

theorem clause21_mixed_transport {O : Type} [Fintype O] {D E : ℕ}
    (P : ConditionalChannelProgram O D E) (h2 : 2 * P.error < P.gap) :
    (transportPureToMixed P.error P.gap).Holds P.actual P.ideal P.selected :=
  pureToMixed_holds P.actual P.ideal P.selected P.error P.gap P.pureCertificate h2

theorem clause21_mixed_transport_bounds {O : Type} [Fintype O] {D E : ℕ}
    (P : ConditionalChannelProgram O D E) (h2 : 2 * P.error < P.gap) :
    0 < P.gap - P.error ∧ 0 ≤ 2 * P.error / (P.gap - P.error) ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      P.gap - P.error ≤ (Matrix.trace (selectedBranch P.ideal P.selected ρ)).re ∧
      0 < (Matrix.trace (selectedBranch P.actual P.selected ρ)).re ∧
      Matrix.traceNorm (normalizedBranch (selectedBranch P.actual P.selected ρ) -
          normalizedBranch (selectedBranch P.ideal P.selected ρ))
        ≤ 2 * P.error / (P.gap - P.error)) := by
  have h : 0 < (transportPureToMixed P.error P.gap).successGap ∧
      0 ≤ (transportPureToMixed P.error P.gap).directionError ∧
      (∀ ρ : Operator D, IsDensityOperator ρ →
        (transportPureToMixed P.error P.gap).successGap ≤
            (Matrix.trace (selectedBranch P.ideal P.selected ρ)).re ∧
          0 < (Matrix.trace (selectedBranch P.actual P.selected ρ)).re ∧
          Matrix.traceNorm (normalizedBranch (selectedBranch P.actual P.selected ρ) -
              normalizedBranch (selectedBranch P.ideal P.selected ρ))
            ≤ (transportPureToMixed P.error P.gap).directionError) :=
    clause21_mixed_transport P h2
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem clause21_zero_mass_branch {O : Type} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) {ρ : Operator D} (hρ : ρ.PosSemidef) (o : O)
    (hzero : instrumentProb I ρ o = 0) :
    I.branch o ρ = 0 ∧ normalizedBranch (I.branch o ρ) = 0 := by
  constructor
  · exact (instrumentProb_eq_zero_iff I hρ o).mp hzero
  · rw [(instrumentProb_eq_zero_iff I hρ o).mp hzero]
    unfold Qatlib.Concepts.MbqcFlow.FlowDecision.normalizedBranch
    simp

theorem clause21_hhl_caller_ledger {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (d : ℝ) (hd : 0 < d)
    (B U : Operator D) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (sinEnvelopeHHLWord M hM d B)
        = 2 * (M - 1) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (sinEnvelopeHHLWord M hM d B)
        = 4 * (M - 1) + 6 ∧
      hhlCallerLedger M = ⟨2 * (M - 1), 4 * (M - 1) + 6⟩ := by
  have h := sin_envelope_word_legality_and_counts D M hM d hd B U hB hU
  exact ⟨h.2.2.1, h.2.2.2, rfl⟩

theorem clause21_ae_caller_ledger {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) :
    aeForwardAccesses (aeAccessWord (I := I) M) = M ∧
    aeBackwardAccesses (aeAccessWord (I := I) M) = M - 1 ∧
    aeInputAccesses (aeAccessWord (I := I) M) = 2 * (M - 1) + 1 ∧
    aeSourceReflections (aeAccessWord (I := I) M) = M - 1 ∧
    aeFixedMacros (aeFlagAccessWord (I := I) M) +
        aeFixedMacros (aeFourierAccessWord (I := I) M) = 2 * (M - 1) + 2 ∧
    aeCallerLedger M = ⟨2 * (M - 1) + 1 + (M - 1), 2 * (M - 1) + 2⟩ := by
  have h1 := prepared_ae_separate_access_counts (I := I) M hM
  have h2 := prepared_ae_access_ledger (I := I) M hM A j
  refine ⟨h1.1, h1.2.1, h2.2.2.1, h2.2.2.2, ?_, rfl⟩
  rw [h1.2.2.1, h1.2.2.2]

theorem clause21_statistics_caller_ledger {I : Type} [Fintype I] [DecidableEq I]
    (M r : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) :
    QueryCount (RepeatCircuit (countedAECircuit M (payoffPreparation A f) (j, false))
      (2 * r + 1)) = (2 * r + 1) * (M - 1) ∧
    GateCount (RepeatCircuit (countedAECircuit M (payoffPreparation A f) (j, false))
      (2 * r + 1)) = (2 * r + 1) * (5 * (M - 1) + 3) ∧
    statisticsCallerLedger M r =
      ⟨(2 * r + 1) * (M - 1), (2 * r + 1) * (5 * (M - 1) + 3)⟩ := by
  have h := quantum_mean_repeated_actual_accesses M r hM A j f
  refine ⟨by simpa using! h.1, by simpa using! h.2, rfl⟩

theorem clause21_caller_budgets (M r : ℕ) :
    (hhlCallerLedger M).withinBudget
        (⟨2 * (M - 1), 4 * (M - 1) + 6⟩ : CallerAccessBudget) ∧
    (aeCallerLedger M).withinBudget
        (⟨2 * (M - 1) + 1 + (M - 1), 2 * (M - 1) + 2⟩ : CallerAccessBudget) ∧
    (statisticsCallerLedger M r).withinBudget
        (⟨(2 * r + 1) * (M - 1), (2 * r + 1) * (5 * (M - 1) + 3)⟩ : CallerAccessBudget) ∧
    hhlCallerLedger M ≠ aeCallerLedger M ∧
    aeCallerLedger M ≠ statisticsCallerLedger M r := by
  refine ⟨⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩, ?_, ?_⟩
  · intro h
    have h1 : 4 * (M - 1) + 6 = 2 * (M - 1) + 2 := by
      have hh := congrArg CallerAccessLedger.macroGateAccesses h
      simpa [hhlCallerLedger, aeCallerLedger] using! hh
    rcases M with (_ | k)
    · simp only [Nat.zero_sub] at h1
      omega
    · simp only [Nat.succ_sub_one] at h1
      omega
  · intro h
    have h1 : 2 * (M - 1) + 2 = (2 * r + 1) * (5 * (M - 1) + 3) := by
      have hh := congrArg CallerAccessLedger.macroGateAccesses h
      simpa [aeCallerLedger, statisticsCallerLedger] using! hh
    rcases M with (_ | k)
    · simp only [Nat.zero_sub] at h1
      have h2 : 3 ≤ (2 * r + 1) * 3 := by
        simpa using! (Nat.mul_le_mul_right 3 (by omega : (1 : ℕ) ≤ 2 * r + 1))
      omega
    · simp only [Nat.succ_sub_one] at h1
      have h2 : 5 * k + 3 ≤ (2 * r + 1) * (5 * k + 3) := by
        simpa using! (Nat.mul_le_mul_right (5 * k + 3) (by omega : (1 : ℕ) ≤ 2 * r + 1))
      omega

theorem clause21_caller_success_gaps :
    0 < callerSuccessGap .hhl ∧ 0 < callerSuccessGap .amplitudeEstimation ∧
    0 < callerSuccessGap .statistics ∧
    callerSuccessGap .hhl ≠ callerSuccessGap .amplitudeEstimation ∧
    callerSuccessGap .amplitudeEstimation ≠ callerSuccessGap .statistics := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi2 : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_pos]
  have hpi2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have h8 : (8 : ℝ) / Real.pi ^ 2 > 1 / 2 := by
    have h2 : (1 / 2 : ℝ) < 8 / Real.pi ^ 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
      linarith
    exact h2
  refine ⟨by norm_num [callerSuccessGap], by simp [callerSuccessGap]; linarith,
    by norm_num [callerSuccessGap], ?_, ?_⟩
  · intro h
    simp only [callerSuccessGap] at h
    linarith
  · intro h
    simp only [callerSuccessGap] at h
    have hpi2pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
    have hhalf : (8 : ℝ) / Real.pi ^ 2 < 1 := by
      rw [div_lt_one hpi2pos]
      linarith
    have hninth : (1 : ℝ) / 9 < 1 / 2 := by norm_num
    linarith

theorem clause22_relative_ae_same_record {I : Type} [Fintype I] [DecidableEq I] (M k N : ℕ)
    (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let a := MeasureProb (preparedAAState A j) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |((N : ℚ) * nativeAEDecode M k z : ℝ) - (N : ℝ) * a| ≤ (N : ℝ) *
        (2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 +
          ((2 : ℝ)⁻¹) ^ k)),
      (aeLaw M A j S hA hM).prob z) ≥ 8 / Real.pi ^ 2 ∧
    (∀ z : Fin M, (a = 0 ∧ z.val = 0) → nativeAEDecode M k z = 0) :=
  native_ae_counting_relative_output_consumer I M k N hM A j S hA

theorem clause22_integer_bit_cost (x : ℚ) (k : ℕ) (M : ℕ) (z : Fin M) :
    nativeAESinCounted x k = (nativeAESin x k, 8 * (k + 8)) ∧
    0 ≤ nativeAEDecode M k z ∧ nativeAEDecode M k z ≤ 1 ∧
    |(nativeAEDecode M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := by
  refine ⟨nativeAESin_value_and_terms x k, native_ae_computed_scalar_precision M k z⟩

theorem clause22_variance_only_sample_budget {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (f : O → ℝ)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    (povmLaw Λ ρ hρ).probEvent (fun ω : Fin L → O =>
      ε < |FinDist.avg f ω - (povmLaw Λ ρ hρ).expect f|)
      ≤ (povmLaw Λ ρ hρ).variance f / (L * ε ^ 2) :=
  FinDist.chebyshev_avg (povmLaw Λ ρ hρ) f hL ε hε

theorem clause22_record_variance {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (f : O → ℝ) :
    (povmLaw Λ ρ hρ).variance f =
      ∑ o, (↑(Λ.mats o) * ρ).trace.re * (f o - (povmLaw Λ ρ hρ).expect f) ^ 2 :=
  povm_variance Λ ρ hρ f

theorem clause22_variance_only_sample_count {O : Type} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (f : O → ℝ)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (_hδ : 0 < δ)
    (hvar : (povmLaw Λ ρ hρ).variance f ≤ δ * (L : ℝ) * ε ^ 2) :
    (povmLaw Λ ρ hρ).probEvent (fun ω : Fin L → O =>
      ε < |FinDist.avg f ω - (povmLaw Λ ρ hρ).expect f|) ≤ δ := by
  have h := clause22_variance_only_sample_budget Λ ρ hρ f L hL ε hε
  have hnonneg : 0 < (L : ℝ) * ε ^ 2 := by positivity
  have h2 : (povmLaw Λ ρ hρ).variance f / (L * ε ^ 2) ≤ δ := by
    rw [div_le_iff₀ hnonneg]
    have : δ * (L : ℝ) * ε ^ 2 = δ * ((L : ℝ) * ε ^ 2) := by ring
    linarith
  exact h.trans h2

theorem clause22_repetition_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, (8 / 9 : ℝ) ^ r ≤ δ / 2 := by
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < δ / 2 by linarith)
    (show (8 : ℝ) / 9 < 1 by
      rw [div_lt_one (by norm_num : (0 : ℝ) < 9)]
      norm_num)
  exact ⟨r, le_of_lt hr⟩

theorem clause22_unknown_variance_total_failure {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (N h r : ℕ) (f : I → ℚ) (nu eps : ℚ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (δ : ℝ) (_hδ : 0 < δ)
    (hpilot : 2 / ((N : ℝ) * (nu : ℝ) ^ 2) ≤ δ / 2)
    (hrep : (8 / 9 : ℝ) ^ r ≤ δ / 2) :
    (∑ z ∈ Finset.univ.filter (fun z : PilotMeanRecord I N h r f nu eps =>
      (eps : ℝ) < |pilotMeanReadout N h r f nu eps z -
        (signedMeanSource A j hA).expect (fun i => (f i : ℝ))|),
      pilotMeanMass A j N h r f nu eps hA z) ≤ δ := by
  have h := (unknown_variance_pilot_same_joint_quantum_mean_probability
    I A j N h r f nu eps hA hN hf hnu hnu1 heps).2.2
  linarith

end Qatlib.Papers.FixedPtSearch14.FixedPoint
