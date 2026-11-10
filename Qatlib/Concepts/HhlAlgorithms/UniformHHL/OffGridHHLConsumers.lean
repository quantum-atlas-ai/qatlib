/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.UniformHHL.OffGridSignedHHL
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.UniformHHL

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable def uniformHHLExampleSpectrum (i : Fin 2) : ℝ := if i = 0 then 1 / 10 else -1 / 8

def uniformHHLExampleDirection (i : Fin 2) : ℂ := if i = 0 then 5 else -4

theorem uniformHHLExampleDirection_norm :
    ‖toEuclidean_fromVec uniformHHLExampleDirection‖ = Real.sqrt 41 := by
  have hs : ‖toEuclidean_fromVec uniformHHLExampleDirection‖ ^ 2 = 41 := by
    rw [norm_toEuclidean_fromVec_sq, Fin.sum_univ_two]
    norm_num [uniformHHLExampleDirection, Complex.normSq_apply]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem uniformHHLExampleSpectrum_promise :
    ∀ i, (1 / 16 : ℝ) ≤ |uniformHHLExampleSpectrum i| ∧
      |uniformHHLExampleSpectrum i| ≤ 1 / 4 := by
  intro i
  fin_cases i <;> norm_num [uniformHHLExampleSpectrum]

theorem uniformHHLExample_inverse :
    matrixPseudoinverse (continuousHHLMatrix uniformHHLExampleSpectrum (1 : Operator 2)) *ᵥ
      (relabelGate boolEquivFin2 Hadamard *ᵥ Ket 0) =
      (Real.sqrt 2 : ℂ) • uniformHHLExampleDirection := by
  have hne : ∀ i, (uniformHHLExampleSpectrum i : ℂ) ≠ 0 := by
    intro i
    fin_cases i <;> norm_num [uniformHHLExampleSpectrum]
  rw [continuousHHLMatrix, pseudoinverse_conj_diagonal _ hne 1 (Submonoid.one_mem _)]
  simp only [one_mul, mul_one, one_conjTranspose]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal_apply,
      relabelGate_submatrix, Hadamard, boolEquivFin2, Ket,
      uniformHHLExampleSpectrum, uniformHHLExampleDirection] <;>
    field_simp <;> ring_nf
  all_goals rw [sqrt2_sq]; norm_num

theorem uniformHHLExample_target (M : ℕ) (hM : 2 ≤ M) :
    uniformHHLSolutionTarget M hM uniformHHLExampleSpectrum (1 : Operator 2)
      (relabelGate boolEquivFin2 Hadamard) 0 =
      uniformHHLSuccessEmbed M hM (fun i : Fin 2 =>
        if i = 0 then (5 / Real.sqrt 41 : ℝ) else (-4 / Real.sqrt 41 : ℝ)) := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hs41 : (Real.sqrt 41 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hn : ‖toEuclidean_fromVec ((Real.sqrt 2 : ℂ) • uniformHHLExampleDirection)‖ =
      Real.sqrt 2 * Real.sqrt 41 := by
    change ‖(Real.sqrt 2 : ℂ) • toEuclidean_fromVec uniformHHLExampleDirection‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), uniformHHLExampleDirection_norm]
  unfold uniformHHLSolutionTarget
  rw [uniformHHLExample_inverse]
  (try dsimp only)
  rw [hn]
  congr 1
  funext i
  fin_cases i <;>
    norm_num [uniformHHLExampleDirection, Pi.smul_apply, smul_eq_mul] <;>
    field_simp

theorem uniform_signed_hhl_tenth_and_eighth_real_consumer :
    ∀ (k : ℕ), let d : ℝ := 1 / 16
      let M := uniformHHLGrid d k
      let hM := uniformHHLGrid_ge_two d k
      let eig : Fin 2 → ℝ := fun i => if i = 0 then 1 / 10 else -1 / 8
      let B : Operator 2 := relabelGate boolEquivFin2 Hadamard
      let out := uniformHHLRun M hM (continuousHHLOracle eig (1 : Operator 2)) d B 0
      let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin 2)) => p.2.2.1 = true)
      let target : QState (Fin 2) := fun i =>
        if i = 0 then (5 / Real.sqrt 41 : ℝ) else (-4 / Real.sqrt 41 : ℝ)
      1 / 1024 ≤ MeasureProb out S ∧
        uniformHHLSolutionTarget M hM eig (1 : Operator 2) B 0 =
          uniformHHLSuccessEmbed M hM target ∧
        ‖toEuclidean_fromVec (PostMeasure out S - uniformHHLSuccessEmbed M hM target)‖ ≤
          32 * min (1 / 32 : ℝ) ((1 / 2 : ℝ) ^ k) := by
  intro k
  (try dsimp only)
  have hp := uniform_hhl_computed_finite_precision_parameters (1 / 16) k (by norm_num)
  have hB : relabelGate boolEquivFin2 Hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (relabelGate_mem_unitaryGroup boolEquivFin2 Hadamard).2 hadamard_unitary
  have h := uniform_offgrid_signed_hhl_born_and_solution 2
    (uniformHHLGrid (1 / 16) k) (uniformHHLGrid_ge_two (1 / 16) k)
    uniformHHLExampleSpectrum 1 (relabelGate boolEquivFin2 Hadamard) 0
    (1 / 16) (uniformHHLAccuracy (1 / 16) k) (Submonoid.one_mem _) hB
    (by norm_num) hp.1 hp.2.1 uniformHHLExampleSpectrum_promise (uniformHHLGrid_budget _ _)
  have ht := uniformHHLExample_target (uniformHHLGrid (1 / 16) k) (uniformHHLGrid_ge_two _ _)
  refine ⟨?_, ht, ?_⟩
  · convert! h.1 using 1; norm_num
  · rw [ht] at h
    convert! h.2.2 using 1; norm_num [uniformHHLAccuracy]
    ring

noncomputable def uniformHHLFlagTrialLaw {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) : PMF Bool :=
  PMF.ofFintype (fun o => ENNReal.ofReal (ProjectiveBranchMass (Projector S) o ψ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => projectiveBranchMass_nonneg _ o ψ),
      Fintype.sum_bool, add_comm (ProjectiveBranchMass (Projector S) true ψ),
      projectiveBranchMass_add (projector_isOrthogonalProjector S),
      measureProb_univ hψ, ENNReal.ofReal_one])

theorem uniformHHLFlagTrialLaw_true {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) :
    uniformHHLFlagTrialLaw ψ hψ S true = ENNReal.ofReal (MeasureProb ψ S) := by
  change ENNReal.ofReal (MeasureProb (Collapse ψ S) Finset.univ) = _
  rw [measureProb_collapse, Finset.inter_univ]

noncomputable def uniformHHLFirstSuccess (trial : PMF Bool) : ℕ → PMF (Bool × ℕ)
  | 0 => PMF.pure (false, 0)
  | R + 1 => trial.bind (fun o => if o then PMF.pure (true, 1)
      else (uniformHHLFirstSuccess trial R).map (fun z => (z.1, z.2 + 1)))

theorem uniformHHLFirstSuccess_attempts (trial : PMF Bool) (R : ℕ) :
    ∀ z ∈ (uniformHHLFirstSuccess trial R).support, z.2 ≤ R := by
  induction R with
  | zero =>
    intro z hz
    have he : z = (false, 0) := by simpa [uniformHHLFirstSuccess] using! hz
    subst z
    simp
  | succ R ih =>
    intro z hz
    obtain ⟨o, ho, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    cases o
    · obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      exact Nat.succ_le_succ (ih w hw)
    · have he : z = (true, 1) := by simpa using! hz
      subst z
      omega

theorem uniformHHL_trial_total (trial : PMF Bool) : trial true + trial false = 1 := by
  simpa only [tsum_fintype, Fintype.sum_bool] using! trial.tsum_coe

theorem uniformHHL_expectation_bool (trial : PMF Bool) (f : Bool → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation trial f = trial true * f true + trial false * f false := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
      Fintype.sum_bool]

theorem uniformHHLFirstSuccess_expected_succ (trial : PMF Bool) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (uniformHHLFirstSuccess trial (R + 1)) (fun z => (z.2 : ℝ≥0∞)) =
      1 + trial false * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (uniformHHLFirstSuccess trial R)
        (fun z => (z.2 : ℝ≥0∞)) := by
  have hmap : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      ((uniformHHLFirstSuccess trial R).map (fun z : Bool × ℕ => (z.1, z.2 + 1)))
      (fun z : Bool × ℕ => (z.2 : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (uniformHHLFirstSuccess trial R) (fun z => (z.2 : ℝ≥0∞)) + 1 := by
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
  rw [uniformHHLFirstSuccess, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
      uniformHHL_expectation_bool]
  simp only [Bool.false_eq_true, if_false, if_true,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, Nat.cast_one]
  rw [hmap]
  have ht := uniformHHL_trial_total trial
  rw [mul_add, ← add_assoc, mul_one, mul_one, add_right_comm, ht]

theorem uniformHHLFirstSuccess_expected_le (trial : PMF Bool) (hp : trial true ≠ 0) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (uniformHHLFirstSuccess trial R) (fun z => (z.2 : ℝ≥0∞)) ≤
      (trial true)⁻¹ := by
  induction R with
  | zero => simp [uniformHHLFirstSuccess]
  | succ R ih =>
    rw [uniformHHLFirstSuccess_expected_succ]
    have hcancel : trial true * (trial true)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hp (PMF.apply_ne_top _ _)
    calc 1 + trial false * _ ≤ 1 + trial false * (trial true)⁻¹ :=
        add_le_add_right (mul_le_mul_right ih _) _
      _ = (trial true + trial false) * (trial true)⁻¹ := by rw [add_mul, hcancel]
      _ = (trial true)⁻¹ := by rw [uniformHHL_trial_total, one_mul]

theorem uniformHHLFirstSuccess_failure (trial : PMF Bool) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R) (fun z => z.1 = false) =
      trial false ^ R := by
  induction R with
  | zero => simp [uniformHHLFirstSuccess, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
  | succ R ih =>
    rw [uniformHHLFirstSuccess, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
      uniformHHL_expectation_bool]
    simp only [Bool.false_eq_true, if_false, if_true, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, Bool.true_eq_false, mul_zero, zero_add]
    change trial false * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R)
      (fun z => z.1 = false) = _
    rw [ih, pow_succ']

theorem uniformHHL_bool_event_total (q : PMF (Bool × ℕ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun z => z.1 = true) + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun z => z.1 = false) = 1 := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation q (fun _ => 1) := by
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      cases z.1 <;> simp
    _ = 1 := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const q 1

theorem uniformHHLFirstSuccess_success (trial : PMF Bool) (R : ℕ) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R) (fun z => z.1 = true)).toReal =
      1 - (1 - (trial true).toReal) ^ R := by
  have htotal := uniformHHL_bool_event_total (uniformHHLFirstSuccess trial R)
  have htr := uniformHHL_trial_total trial
  have htrreal : (trial true).toReal + (trial false).toReal = 1 := by
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), htr]
    norm_num
  have hsuccess : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R) (fun z => z.1 = true) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((le_add_right le_rfl).trans_eq htotal)
  have hfailure : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R) (fun z => z.1 = false) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((le_add_left le_rfl).trans_eq htotal)
  have hreal : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R) (fun z => z.1 = true)).toReal +
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLFirstSuccess trial R) (fun z => z.1 = false)).toReal = 1 := by
    rw [← ENNReal.toReal_add hsuccess hfailure, htotal]
    norm_num
  rw [uniformHHLFirstSuccess_failure, ENNReal.toReal_pow] at hreal
  have hf : (trial false).toReal = 1 - (trial true).toReal := by linarith
  rw [hf] at hreal
  linarith

noncomputable def uniformHHLRetryLaw {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (R : ℕ) :
    CostedLaw (Bool × ℕ × ℕ × ℕ) :=
  let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
  let hout : Normalized out := (Qatlib.Concepts.BlockEncoding.Postselection.normalized_iff_stateVector_norm out).2
    (uniformHHLRun_norm M hM _ B j d (continuous_hhl_oracle_unitary eig V hV) hB hd)
  let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)
  (uniformHHLFirstSuccess (uniformHHLFlagTrialLaw out hout S) R).map
    (fun z => ((z.1, z.2, z.2 * (4 * (M - 1) + 6), z.2), z.2 * (2 * (M - 1))))

theorem uniformHHLRetryLaw_zero {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) :
    uniformHHLRetryLaw M hM eig V d B j hV hB hd 0 = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (false, 0, 0, 0) := by
  simp [uniformHHLRetryLaw, uniformHHLFirstSuccess, PMF.pure_map,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret]

theorem uniformHHLRetryLaw_ledger {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (R : ℕ) :
    ∀ z ∈ (uniformHHLRetryLaw M hM eig V d B j hV hB hd R).support,
      z.1.2.1 ≤ R ∧ z.1.2.2.1 = z.1.2.1 * (4 * (M - 1) + 6) ∧
      z.1.2.2.2 = z.1.2.1 ∧ z.2 = z.1.2.1 * (2 * (M - 1)) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  exact ⟨uniformHHLFirstSuccess_attempts _ R w hw, rfl, rfl, rfl⟩

theorem uniformHHLRetryLaw_success {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (R : ℕ) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (uniformHHLRetryLaw M hM eig V d B j hV hB hd R)
      (fun z => z.1.1 = true)).toReal =
      1 - (1 - MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig V) d B j)
        (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true))) ^ R := by
  unfold uniformHHLRetryLaw
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, uniformHHLFirstSuccess_success, uniformHHLFlagTrialLaw_true,
    ENNReal.toReal_ofReal (measureProb_nonneg _ _)]

theorem uniformHHLRetryLaw_expected_le {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (R : ℕ)
    (hp : 0 < MeasureProb (uniformHHLRun M hM (continuousHHLOracle eig V) d B j)
      (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true))) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (uniformHHLRetryLaw M hM eig V d B j hV hB hd R) ≤
      (2 * (M - 1) : ℕ) / ENNReal.ofReal (MeasureProb
        (uniformHHLRun M hM (continuousHHLOracle eig V) d B j)
        (Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true))) := by
  unfold uniformHHLRetryLaw
  (try dsimp only)
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp only [Nat.cast_mul]
  have he : ∀ (q : PMF (Bool × ℕ)) (c : ℝ≥0∞),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation q (fun z => (z.2 : ℝ≥0∞) * c) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation q (fun z => (z.2 : ℝ≥0∞)) * c := by
    intro q c
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
        ← ENNReal.tsum_mul_right, mul_assoc]
  rw [he]
  let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
  let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)
  have hout : Normalized out := (Qatlib.Concepts.BlockEncoding.Postselection.normalized_iff_stateVector_norm out).2
    (uniformHHLRun_norm M hM _ B j d (continuous_hhl_oracle_unitary eig V hV) hB hd)
  let trial := uniformHHLFlagTrialLaw out hout S
  have htrial : trial true ≠ 0 := by
    rw [uniformHHLFlagTrialLaw_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hbnd := uniformHHLFirstSuccess_expected_le trial htrial R
  have h := mul_le_mul_left hbnd ((2 * (M - 1) : ℕ) : ℝ≥0∞)
  rw [uniformHHLFlagTrialLaw_true] at h
  simpa only [div_eq_mul_inv, Nat.cast_mul, mul_comm] using! h

theorem uniform_offgrid_hhl_fresh_retry_success_and_cost :
    ∀ (D M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ) (V B : Operator D)
      (j : Fin D) (d η : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (R : ℕ),
      0 < η → η ≤ d / 2 → (∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4) →
      4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ) →
      let q := uniformHHLRetryLaw M hM eig V d B j hV hB hd R
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun z => z.1.1 = true)).toReal ≥ 1 - (1 - d ^ 2 / 4) ^ R ∧
        (∀ z ∈ q.support, z.1.2.1 ≤ R ∧ z.1.2.2.1 = z.1.2.1 * (4 * (M - 1) + 6) ∧
          z.1.2.2.2 = z.1.2.1 ∧ z.2 = z.1.2.1 * (2 * (M - 1))) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost q ≤ (8 * (M - 1 : ℕ) : ℝ≥0∞) / (ENNReal.ofReal d) ^ 2 := by
  intro D M hM eig V B j d η hV hB hd R hη hηd heig hbudget
  (try dsimp only)
  let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
  let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)
  have hborn := uniform_offgrid_signed_hhl_born_and_solution D M hM eig V B j d η
    hV hB hd hη hηd heig hbudget
  have hout : Normalized out := (Qatlib.Concepts.BlockEncoding.Postselection.normalized_iff_stateVector_norm out).2
    (uniformHHLRun_norm M hM _ B j d (continuous_hhl_oracle_unitary eig V hV) hB hd)
  have hp1 : MeasureProb out S ≤ 1 := measureProb_le_one hout S
  refine ⟨?_, uniformHHLRetryLaw_ledger M hM eig V d B j hV hB hd R, ?_⟩
  · rw [uniformHHLRetryLaw_success]
    change 1 - (1 - d ^ 2 / 4) ^ R ≤ 1 - (1 - MeasureProb out S) ^ R
    have hf : 1 - MeasureProb out S ≤ 1 - d ^ 2 / 4 := by linarith [hborn.1]
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - MeasureProb out S) hf R
    linarith
  · have he := uniformHHLRetryLaw_expected_le M hM eig V d B j hV hB hd R hborn.2.1
    have hp : ENNReal.ofReal (d ^ 2 / 4) ≤ ENNReal.ofReal (MeasureProb out S) :=
      ENNReal.ofReal_le_ofReal hborn.1
    have hdiv := ENNReal.div_le_div_left hp ((2 * (M - 1) : ℕ) : ℝ≥0∞)
    refine he.trans (hdiv.trans_eq ?_)
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_pow hd.le]
    norm_num
    rw [div_eq_mul_inv, ENNReal.inv_div (by left; norm_num) (by left; norm_num)]
    simp only [div_eq_mul_inv]
    ring

theorem uniformHHLRetry_success_state {D M : ℕ} (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (hη : 0 < η) (hηd : η ≤ d / 2)
    (heig : ∀ i, d ≤ |eig i| ∧ |eig i| ≤ 1 / 4)
    (hbudget : 4096 / (d ^ 2 * η ^ 4) ≤ (M : ℝ)) :
    let out := uniformHHLRun M hM (continuousHHLOracle eig V) d B j
    let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin D)) => p.2.2.1 = true)
    ProjectiveConditionalState (Projector S) true out = some (PostMeasure out S) := by
  (try dsimp only)
  rw [ProjectiveConditionalState, projectiveBranch_projector]
  exact conditionalState_collapse
    (uniform_offgrid_signed_hhl_born_and_solution D M hM eig V B j d η
      hV hB hd hη hηd heig hbudget).2.1

theorem uniformHHLExample_fresh_retry (k R : ℕ) :
    let d : ℝ := 1 / 16
    let M := uniformHHLGrid d k
    let hM := uniformHHLGrid_ge_two d k
    let B := relabelGate boolEquivFin2 Hadamard
    let hV : (1 : Operator 2) ∈ Matrix.unitaryGroup (Fin 2) ℂ := Submonoid.one_mem _
    let hB := (relabelGate_mem_unitaryGroup boolEquivFin2 Hadamard).2 hadamard_unitary
    let hd : 0 < d := by norm_num
    let out := uniformHHLRun M hM (continuousHHLOracle uniformHHLExampleSpectrum 1) d B 0
    let S := Finset.univ.filter (fun p : Fin M × (Bool × (Bool × Fin 2)) => p.2.2.1 = true)
    let q := uniformHHLRetryLaw M hM uniformHHLExampleSpectrum 1 d B 0 hV hB hd R
    1 / 1024 ≤ MeasureProb out S ∧
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event q (fun z => z.1.1 = true)).toReal ≥ 1 - (1023 / 1024 : ℝ) ^ R ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost q ≤ 2048 * (M - 1 : ℕ) := by
  (try dsimp only)
  have hp := uniform_hhl_computed_finite_precision_parameters (1 / 16) k (by norm_num)
  have h := uniform_offgrid_hhl_fresh_retry_success_and_cost 2
    (uniformHHLGrid (1 / 16) k) (uniformHHLGrid_ge_two _ _)
    uniformHHLExampleSpectrum 1 (relabelGate boolEquivFin2 Hadamard) 0
    (1 / 16) (uniformHHLAccuracy (1 / 16) k) (Submonoid.one_mem _)
    ((relabelGate_mem_unitaryGroup boolEquivFin2 Hadamard).2 hadamard_unitary)
    (by norm_num) R hp.1 hp.2.1 uniformHHLExampleSpectrum_promise (uniformHHLGrid_budget _ _)
  refine ⟨(uniform_signed_hhl_tenth_and_eighth_real_consumer k).1, ?_, ?_⟩
  · convert! h.1 using 1; norm_num
  · convert! h.2.2 using 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
    norm_num
    rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow, inv_inv]
    norm_num
    ring

noncomputable def uniformHHLRetrySelectedState {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) (result : Bool × ℕ) : Option (QState I) :=
  if result.1 then ProjectiveConditionalState (Projector S) true ψ else none

theorem uniformHHLRetrySelectedState_success {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) (result : Bool × ℕ)
    (hs : result.1 = true) (hp : 0 < MeasureProb ψ S) :
    uniformHHLRetrySelectedState ψ S result = some (PostMeasure ψ S) := by
  rw [uniformHHLRetrySelectedState, hs, if_pos rfl, ProjectiveConditionalState,
    projectiveBranch_projector]
  exact conditionalState_collapse hp

end Qatlib.Concepts.HhlAlgorithms.UniformHHL
