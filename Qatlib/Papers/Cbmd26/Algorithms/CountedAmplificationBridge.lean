/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.Cbmd26.Algorithms.OuterBridge
import Qatlib.Papers.Cbmd26.Algorithms.QueryCostBridge
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
set_option warningAsError false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
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
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal Classical

variable {H : Type} [Fintype H] [DecidableEq H]

def countedAAWord (body : List (PreparedStep H)) (zero : H) (S : Finset H) :
    ℕ → List (PreparedStep H)
  | 0 => body
  | k + 1 => body ++ [.gate (ReflectionAbout (outerProduct (Ket zero)))] ++
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord body ++ [.gate (preparedMark S)] ++
      countedAAWord body zero S k

omit [Fintype H] [DecidableEq H] in

private theorem aa_counts_append (cs ds : List (PreparedStep H)) :
    preparedDataQueries (cs ++ ds) = preparedDataQueries cs + preparedDataQueries ds ∧
    preparedInputQueries (cs ++ ds) = preparedInputQueries cs + preparedInputQueries ds ∧
    preparedFixedGates (cs ++ ds) = preparedFixedGates cs + preparedFixedGates ds :=
  preparedCounts_append cs ds

theorem countedAAWord_evaluate (O B : Matrix H H ℂ) (body : List (PreparedStep H))
    (zero : H) (S : Finset H) (k : ℕ) :
    evaluatePrepared O B (countedAAWord body zero S k) =
      (preparedAAIterate (evaluatePrepared O B body) zero S) ^ k * evaluatePrepared O B body := by
  induction k with
  | zero => simp [countedAAWord]
  | succ k ih =>
    simp only [countedAAWord, evaluatePrepared_append, evaluatePrepared,
      preparedInstruction, Matrix.mul_one, Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_evaluate, ih,
      pow_succ', preparedAAIterate, Matrix.mul_assoc]

theorem countedAAWord_counts (body : List (PreparedStep H)) (zero : H) (S : Finset H)
    (k : ℕ) :
    preparedDataQueries (countedAAWord body zero S k) = (2 * k + 1) * preparedDataQueries body ∧
    preparedInputQueries (countedAAWord body zero S k) = (2 * k + 1) * preparedInputQueries body ∧
    preparedFixedGates (countedAAWord body zero S k) =
      (2 * k + 1) * preparedFixedGates body + 2 * k := by
  induction k with
  | zero => simp [countedAAWord]
  | succ k ih =>
    simp only [countedAAWord, (aa_counts_append _ _).1, (aa_counts_append _ _).2.1,
      (aa_counts_append _ _).2.2, (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_counts _).1,
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_counts _).2.1, (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_counts _).2.2,
      preparedDataQueries, preparedInputQueries, preparedFixedGates, ih.1, ih.2.1, ih.2.2]
    constructor
    · ring
    constructor <;> ring

private theorem aa_valid_append {cs ds : List (PreparedStep H)}
    (hc : PreparedCircuitValid cs) (hd : PreparedCircuitValid ds) :
    PreparedCircuitValid (cs ++ ds) := by
  intro c h
  exact (List.mem_append.mp h).elim (hc c) (hd c)

theorem countedAAWord_valid (body : List (PreparedStep H)) (zero : H) (S : Finset H)
    (k : ℕ) (hbody : PreparedCircuitValid body) :
    PreparedCircuitValid (countedAAWord body zero S k) := by
  have hzero : PreparedCircuitValid
      ([.gate (ReflectionAbout (outerProduct (Ket zero)))] : List (PreparedStep H)) := by
    intro c hc
    have hc' : c = .gate (ReflectionAbout (outerProduct (Ket zero))) := List.mem_singleton.mp hc
    subst c
    exact outerProduct_reflection_unitary (normalized_ket zero)
  have hmark : PreparedCircuitValid ([.gate (preparedMark S)] : List (PreparedStep H)) := by
    intro c hc
    have hc' : c = .gate (preparedMark S) := List.mem_singleton.mp hc
    subst c
    exact (prepared_aa_reflection_and_access (1 : Matrix H H ℂ) zero S
      (Matrix.unitaryGroup H ℂ).one_mem).1
  induction k with
  | zero => exact hbody
  | succ k ih =>
    exact aa_valid_append
      (aa_valid_append (aa_valid_append (aa_valid_append hbody hzero)
        (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_valid hbody)) hmark) ih

theorem countedAAWord_run (O B : Matrix H H ℂ) (body : List (PreparedStep H))
    (zero : H) (S : Finset H) (k : ℕ)
    (hA : evaluatePrepared O B body ∈ Matrix.unitaryGroup H ℂ) :
    ApplyGate (evaluatePrepared O B (countedAAWord body zero S k)) (Ket zero) =
      Run (preparedMark S) (preparedAACircuit (evaluatePrepared O B body) zero k) (Ket zero) := by
  rw [countedAAWord_evaluate, (prepared_aa_actual_circuit _ zero S k hA).2.2.2]
  simp only [preparedAAState, ApplyGate, Matrix.mulVec_mulVec]

theorem countedAAWord_preparedTrial_counts (cs : List (AdjointStep H)) (zero : H)
    (S : Finset H) (k : ℕ) :
    preparedDataQueries (countedAAWord (preparedTrial cs) zero S k) =
      (2 * k + 1) * adjointQueryCount cs ∧
    preparedInputQueries (countedAAWord (preparedTrial cs) zero S k) = 2 * k + 1 ∧
    preparedFixedGates (countedAAWord (preparedTrial cs) zero S k) =
      (2 * k + 1) * adjointGateCount cs + 2 * k := by
  obtain ⟨hd, hb, hg⟩ := countedAAWord_counts (preparedTrial cs) zero S k
  obtain ⟨hd', hb', hg'⟩ := preparedTrial_counts cs
  rw [hd'] at hd
  rw [hb', mul_one] at hb
  rw [hg'] at hg
  exact ⟨hd, hb, hg⟩

theorem success_angle_exists (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧ p = (Real.sin θ) ^ 2 := by
  have hs0 := Real.sqrt_nonneg p
  have hsq := Real.sq_sqrt hp.le
  have hs1 : Real.sqrt p < 1 := by nlinarith
  refine ⟨Real.arcsin (Real.sqrt p), Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp),
    Real.arcsin_lt_pi_div_two.mpr hs1, ?_⟩
  rw [Real.sin_arcsin (by linarith) hs1.le, hsq]

theorem randomized_prepared_aa_success (A : Matrix H H ℂ) (zero : H) (S : Finset H)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (r : ℝ) (hr : 0 < r)
    (hp : 1 / r ^ 2 ≤ MeasureProb (preparedAAState A zero) S)
    (m : ℕ) (hm : r ≤ (m : ℝ)) :
    (1 / 8 : ℝ) ≤
      (MeasureProb (preparedAAState A zero) S +
        (∑ i : Fin m, MeasureProb
          (Run (preparedMark S) (preparedAACircuit A zero i.val) (Ket zero)) S) / (m : ℝ)) / 2 := by
  let p := MeasureProb (preparedAAState A zero) S
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hm0 : 0 < m := by exact_mod_cast (lt_of_lt_of_le hr hm)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have havg0 : 0 ≤ (∑ i : Fin m, MeasureProb
      (Run (preparedMark S) (preparedAACircuit A zero i.val) (Ket zero)) S) / (m : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => measureProb_nonneg _ _) hmR.le
  by_cases hhalf : (1 / 2 : ℝ) ≤ p
  · dsimp only [p] at hhalf
    linarith
  · have hpHalf : p < 1 / 2 := lt_of_not_ge hhalf
    obtain ⟨θ, hθ0, hθ1, hθp⟩ := success_angle_exists p hp0 (by linarith)
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    have hsc := Real.sin_sq_add_cos_sq θ
    have hrs : 1 ≤ r * Real.sin θ := by
      have hbase : 1 ≤ r ^ 2 * p := by
        simpa only [p, mul_comm] using! (div_le_iff₀ (sq_pos_of_pos hr)).mp hp
      rw [hθp] at hbase
      apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hr.le hs.le)).mp
      nlinarith
    have hms : 1 ≤ (m : ℝ) * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      have hms0 : 1 ≤ (m : ℝ) * Real.sin θ :=
        hrs.trans (mul_le_mul_of_nonneg_right hm hs.le)
      have hcos : 1 ≤ 2 * Real.cos θ := by rw [hθp] at hpHalf; nlinarith
      have hprod := mul_le_mul hms0 hcos (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hmR.le hs.le)
      nlinarith
    have hlow := prepared_aa_uniform_success_lower A zero S θ m hA hm0 hθ0 hθ1 hθp hms
    linarith

theorem prepared_aa_good_collinear (A : Matrix H H ℂ) (zero : H) (S : Finset H)
    (hA : A ∈ Matrix.unitaryGroup H ℂ)
    (hp : 0 < MeasureProb (preparedAAState A zero) S) (k : ℕ) :
    ∃ z : ℂ, Collapse
      (Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) S =
      z • Collapse (preparedAAState A zero) S := by
  have hp1 := measureProb_le_one (prepared_aa_reflection_and_access A zero S hA).2.1 S
  by_cases hfull : MeasureProb (preparedAAState A zero) S = 1
  · refine ⟨(-1 : ℂ) ^ k, ?_⟩
    rw [(prepared_aa_endpoint_states A zero S k hA).2 hfull]
    funext i
    by_cases hi : i ∈ S <;> simp [collapse_apply, hi]
  · obtain ⟨θ, hθ0, hθ1, hθp⟩ :=
      success_angle_exists _ hp (lt_of_le_of_ne hp1 hfull)
    refine ⟨((Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ), ?_⟩
    rw [prepared_aa_actual_rotation A zero S θ k hA hθ0 hθ1 hθp]
    have hcol : ∀ (a b : ℂ) (u v : QState H),
        Collapse (a • u + b • v) S = a • Collapse u S + b • Collapse v S := by
      intro a b u v
      funext i
      by_cases hi : i ∈ S <;> simp [collapse_apply, hi]
    have hbad : Collapse (preparedAAState A zero - Collapse (preparedAAState A zero) S) S = 0 := by
      funext i
      by_cases hi : i ∈ S <;> simp [collapse_apply, hi]
    have hgood : Collapse (Collapse (preparedAAState A zero) S) S =
        Collapse (preparedAAState A zero) S := by
      funext i
      by_cases hi : i ∈ S <;> simp [collapse_apply, hi]
    rw [hcol, hbad, hgood, smul_zero, zero_add]

def projectiveHeraldLaw (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P)
    (ψ : QState H) (hψ : Normalized ψ) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (ProjectiveBranchMass P b ψ)) (by
    rw [Fintype.sum_bool, add_comm, ← ENNReal.ofReal_add
      (projectiveBranchMass_nonneg P false ψ) (projectiveBranchMass_nonneg P true ψ),
      projectiveBranchMass_add hP, measureProb_univ hψ, ENNReal.ofReal_one])

theorem projectiveHeraldLaw_success (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P)
    (ψ : QState H) (hψ : Normalized ψ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (projectiveHeraldLaw P hP ψ hψ) (fun b => b = true) =
      ENNReal.ofReal (ProjectiveBranchMass P true ψ) := by
  simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype, projectiveHeraldLaw]

def aaRounds {m : ℕ} (choice : Bool × Fin m) : ℕ :=
  if choice.1 then choice.2.val else 0

def aaSchedule (m : ℕ) [NeZero m] : PMF (Bool × Fin m) :=
  PMF.uniformOfFintype' (Bool × Fin m)

def randomizedAAHerald (A : Matrix H H ℂ) (hA : A ∈ Matrix.unitaryGroup H ℂ)
    (zero : H) (S : Finset H) (m : ℕ) [NeZero m] : PMF ((Bool × Fin m) × Bool) :=
  (aaSchedule m).bind fun choice =>
    (projectiveHeraldLaw (Projector S) (projector_isOrthogonalProjector S)
      (Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero))
      ((prepared_aa_actual_circuit A zero S (aaRounds choice) hA).1.normalized_run
        (prepared_aa_reflection_and_access A zero S hA).1 (normalized_ket zero))).map
      (fun success => (choice, success))

theorem aaSchedule_expectation (m : ℕ) [NeZero m] (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (aaSchedule m) (fun c => ENNReal.ofReal (f (aaRounds c))) =
      ENNReal.ofReal ((f 0 + (∑ i : Fin m, f i.val) / (m : ℝ)) / 2) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, aaSchedule, tsum_fintype,
    PMF.uniformOfFintype'_apply, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun c _ => hf (aaRounds c))]
  have he : (((2 * m : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((2 * (m : ℝ))⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    norm_cast
  rw [he, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [Fintype.sum_prod_type, aaRounds]
  field_simp
  ring

theorem randomizedAAHerald_success (A : Matrix H H ℂ) (hA : A ∈ Matrix.unitaryGroup H ℂ)
    (zero : H) (S : Finset H) (m : ℕ) [NeZero m] :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) =
      ENNReal.ofReal ((MeasureProb (preparedAAState A zero) S +
        (∑ i : Fin m, MeasureProb
          (Run (preparedMark S) (preparedAACircuit A zero i.val) (Ket zero)) S) / (m : ℝ)) / 2) := by
  unfold randomizedAAHerald Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  calc
    _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (aaSchedule m) (fun choice => ENNReal.ofReal
        (MeasureProb (Run (preparedMark S)
          (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) S)) := by
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro choice
      simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
          projectiveHeraldLaw]
      congr 1
      exact sum_normSq_collapse _ _
    _ = _ := by
      rw [aaSchedule_expectation m (fun k => MeasureProb
        (Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) S)
        (fun k => measureProb_nonneg _ _)]
      congr 2

theorem randomizedAAHerald_success_lower (A : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (zero : H) (S : Finset H)
    (r : ℝ) (hr : 0 < r)
    (hp : 1 / r ^ 2 ≤ MeasureProb (preparedAAState A zero) S)
    (m : ℕ) [NeZero m] (hm : r ≤ (m : ℝ)) :
    ENNReal.ofReal (1 / 8 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) := by
  rw [randomizedAAHerald_success]
  exact ENNReal.ofReal_le_ofReal (randomized_prepared_aa_success A zero S hA r hr hp m hm)

theorem prepared_aa_decoded_phase {D : Type} [Fintype D] [DecidableEq D]
    (A : Matrix H H ℂ) (zero : H) (S : Finset H) (hA : A ∈ Matrix.unitaryGroup H ℂ)
    (L : Matrix H D ℂ) (hL : IsIsometry L) (hproject : rangeProjector L = Projector S)
    (hp : 0 < MeasureProb (preparedAAState A zero) S)
    (hx : Lᴴ *ᵥ preparedAAState A zero ≠ 0) (k : ℕ)
    (hk : 0 < MeasureProb (Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) S) :
    ∃ (y : QState D) (z : ℂ),
      ConditionalState (Lᴴ *ᵥ Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) = some y ∧
      ‖z‖ = 1 ∧ Normalized y ∧
      (star z) • y = PostMeasure (Lᴴ *ᵥ preparedAAState A zero) Finset.univ := by
  obtain ⟨c, hc⟩ := prepared_aa_good_collinear A zero S hA hp k
  have hdecode (v : QState H) : Lᴴ *ᵥ Collapse v S = Lᴴ *ᵥ v := by
    have hLP : Lᴴ * Projector S = Lᴴ := by
      rw [← hproject, rangeProjector, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    change Lᴴ *ᵥ ((Projector S) *ᵥ v) = _
    rw [Matrix.mulVec_mulVec, hLP]
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    have hmass := sum_normSq_collapse
      (Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) S
    rw [hc] at hmass
    simp only [Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] at hmass
    linarith
  have hdecoded := congrArg (fun v => Lᴴ *ᵥ v) hc

  rw [Matrix.mulVec_smul, hdecode, hdecode] at hdecoded
  obtain ⟨y, z, hy, hz, _, hn, halign⟩ :=
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.conditional_scalar c (Lᴴ *ᵥ preparedAAState A zero) hc0 hx
  refine ⟨y, z, ?_, hz, hn, halign⟩
  rw [hdecoded]
  exact hy

theorem randomizedAAHerald_schedule_observable (A : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (zero : H) (S : Finset H)
    (m : ℕ) [NeZero m] (f : Bool × Fin m → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m) (fun x => f x.1) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (aaSchedule m) f := by
  simp [randomizedAAHerald, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]

theorem sum_odd_indices (m : ℕ) :
    (∑ i : Fin m, (2 * (i.val : ℝ) + 1)) = (m : ℝ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem randomizedAAHerald_input_cost (O B : Matrix H H ℂ)
    (cs : List (AdjointStep H)) (zero : H) (S : Finset H)
    (hA : evaluatePrepared O B (preparedTrial cs) ∈ Matrix.unitaryGroup H ℂ)
    (m : ℕ) [NeZero m] :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (randomizedAAHerald (evaluatePrepared O B (preparedTrial cs)) hA zero S m)
      (fun x => (preparedInputQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal (((m : ℝ) + 1) / 2) := by
  rw [randomizedAAHerald_schedule_observable _ hA zero S m
    (fun c => (preparedInputQueries
      (countedAAWord (preparedTrial cs) zero S (aaRounds c)) : ℝ≥0∞))]
  have hcast (k : ℕ) : (preparedInputQueries
      (countedAAWord (preparedTrial cs) zero S k) : ℝ≥0∞) =
      ENNReal.ofReal (2 * (k : ℝ) + 1) := by
    rw [(countedAAWord_preparedTrial_counts cs zero S k).2.1]
    norm_cast
  simp_rw [hcast]
  rw [aaSchedule_expectation m (fun k => 2 * (k : ℝ) + 1) (fun k => by positivity),
    sum_odd_indices]
  congr 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp
  ring

theorem randomizedAAHerald_data_cost (O B : Matrix H H ℂ)
    (cs : List (AdjointStep H)) (zero : H) (S : Finset H)
    (hA : evaluatePrepared O B (preparedTrial cs) ∈ Matrix.unitaryGroup H ℂ)
    (m : ℕ) [NeZero m] :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (randomizedAAHerald (evaluatePrepared O B (preparedTrial cs)) hA zero S m)
      (fun x => (preparedDataQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (adjointQueryCount cs : ℝ)) := by
  rw [randomizedAAHerald_schedule_observable _ hA zero S m
    (fun c => (preparedDataQueries
      (countedAAWord (preparedTrial cs) zero S (aaRounds c)) : ℝ≥0∞))]
  have hcast (k : ℕ) : (preparedDataQueries
      (countedAAWord (preparedTrial cs) zero S k) : ℝ≥0∞) =
      ENNReal.ofReal ((2 * (k : ℝ) + 1) * (adjointQueryCount cs : ℝ)) := by
    rw [(countedAAWord_preparedTrial_counts cs zero S k).1]
    norm_cast
  simp_rw [hcast]
  rw [aaSchedule_expectation m (fun k => (2 * (k : ℝ) + 1) * (adjointQueryCount cs : ℝ))
    (fun k => by positivity), ← Finset.sum_mul, sum_odd_indices]
  congr 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp
  ring

theorem randomizedAA_path_budget (cs : List (AdjointStep H)) (zero : H) (S : Finset H)
    (m : ℕ) [NeZero m] (choice : Bool × Fin m) :
    preparedInputQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) ≤ 2 * m - 1 ∧
    preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) ≤
      (2 * m - 1) * adjointQueryCount cs := by
  have hk : aaRounds choice < m := by
    unfold aaRounds
    split_ifs
    · exact choice.2.isLt
    · exact Nat.pos_of_ne_zero (NeZero.ne m)
  have hcount : 2 * aaRounds choice + 1 ≤ 2 * m - 1 := by omega
  rw [(countedAAWord_preparedTrial_counts cs zero S _).1,
    (countedAAWord_preparedTrial_counts cs zero S _).2.1]
  exact ⟨hcount, Nat.mul_le_mul_right _ hcount⟩

theorem blockEncoding_prepared_identification {I D : Type} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D]
    (V B : Matrix H H ℂ) (L : Matrix H D ℂ) (R : Matrix H I ℂ)
    (zero : H) (S : Finset H) (ψ : QState I)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S) :
    MeasureProb (preparedAAState (V * B) zero) S = postselectionProbability V L R ψ ∧
    Lᴴ *ᵥ preparedAAState (V * B) zero = postselectionVector V L R ψ := by
  have hstate : preparedAAState (V * B) zero = ApplyGate V (R *ᵥ ψ) := by
    simp only [preparedAAState, ApplyGate, ← Matrix.mulVec_mulVec]
    rw [show B *ᵥ Ket zero = R *ᵥ ψ from hprepare]
  constructor
  · unfold postselectionProbability
    rw [hproject, ← hstate]
    exact (sum_normSq_collapse _ _).symm
  · rw [hstate]
    simp only [postselectionVector, compress, ApplyGate, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]

theorem blockEncoding_prepared_success_lower {I D : Type} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D]
    (target : Matrix D I ℂ) (V B : Matrix H H ℂ)
    (L : Matrix H D ℂ) (R : Matrix H I ℂ) (scale error η : ℝ)
    (henc : BlockEncoding target V L R scale error)
    (zero : H) (S : Finset H) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S)
    (hη : 0 < η) (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖) (herror : error ≤ η / 2) :
    1 / (2 * scale / η) ^ 2 ≤ MeasureProb (preparedAAState (V * B) zero) S := by
  have ha := henc.normalization_pos
  have hgap : error < ‖stateVector (target *ᵥ ψ)‖ := by linarith
  have hp :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower henc hψ hgap.le
  rw [(blockEncoding_prepared_identification V B L R zero S ψ hprepare hproject).1]
  have hab : η / (2 * scale) ≤ (‖stateVector (target *ᵥ ψ)‖ - error) / scale := by
    apply (le_div_iff₀ ha).2
    have heq : η / (2 * scale) * scale = η / 2 := by field_simp
    rw [heq]
    linarith
  have hb0 : 0 ≤ (‖stateVector (target *ᵥ ψ)‖ - error) / scale := by positivity
  have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ η / (2 * scale)) hb0).mpr hab
  have heq : 1 / (2 * scale / η) ^ 2 = (η / (2 * scale)) ^ 2 := by
    field_simp
  exact heq.trans_le (hsquare.trans hp)

theorem blockEncoding_randomized_success {I D : Type} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D]
    (target : Matrix D I ℂ) (V B : Matrix H H ℂ)
    (L : Matrix H D ℂ) (R : Matrix H I ℂ) (scale error η : ℝ)
    (henc : BlockEncoding target V L R scale error) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (zero : H) (S : Finset H) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S)
    (hη : 0 < η) (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖) (herror : error ≤ η / 2)
    (m : ℕ) [NeZero m] (hwindow : 2 * scale / η ≤ (m : ℝ)) :
    ENNReal.ofReal (1 / 8 : ℝ) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (randomizedAAHerald (V * B) ((Matrix.unitaryGroup H ℂ).mul_mem henc.unitary hB)
        zero S m) (fun x => x.2 = true) := by
  apply randomizedAAHerald_success_lower _ _ zero S (2 * scale / η)
    (div_pos (mul_pos (by norm_num) henc.normalization_pos) hη) _ m hwindow
  exact blockEncoding_prepared_success_lower target V B L R scale error η henc zero S ψ hψ
    hprepare hproject hη htarget herror

theorem blockEncoding_randomized_output {I D : Type} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D]
    (target : Matrix D I ℂ) (V B : Matrix H H ℂ)
    (L : Matrix H D ℂ) (R : Matrix H I ℂ) (scale error : ℝ)
    (henc : BlockEncoding target V L R scale error) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (zero : H) (S : Finset H) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S)
    (hgap : error < ‖stateVector (target *ᵥ ψ)‖) (k : ℕ)
    (hk : 0 < MeasureProb (Run (preparedMark S) (preparedAACircuit (V * B) zero k) (Ket zero)) S) :
    ∃ (y : QState D) (z : ℂ),
      ConditionalState (Lᴴ *ᵥ Run (preparedMark S)
        (preparedAACircuit (V * B) zero k) (Ket zero)) = some y ∧
      ‖z‖ = 1 ∧ Normalized y ∧
      IsNormalizedApplication target ψ ((star z) • y)
        (2 * error / ‖stateVector (target *ᵥ ψ)‖) := by
  obtain ⟨hp, φ, hφ, hspec⟩ :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap henc hψ hgap
  obtain ⟨hprob, hvec⟩ := blockEncoding_prepared_identification V B L R zero S ψ hprepare hproject
  have hcond : ConditionalState (Lᴴ *ᵥ preparedAAState (V * B) zero) = some φ := by
    rw [hvec]
    exact hφ
  have hx : Lᴴ *ᵥ preparedAAState (V * B) zero ≠ 0 := by
    intro hx
    rw [hx, conditionalState_zero] at hcond
    contradiction
  have hnormed : PostMeasure (Lᴴ *ᵥ preparedAAState (V * B) zero) Finset.univ = φ := by
    rw [conditionalState_eq_some_of_ne_zero hx] at hcond
    exact Option.some.inj hcond
  obtain ⟨y, z, hy, hz, hn, halign⟩ := prepared_aa_decoded_phase (V * B) zero S
    ((Matrix.unitaryGroup H ℂ).mul_mem henc.unitary hB) L henc.left_isometry hproject
    (hprob.symm ▸ hp) hx k hk
  refine ⟨y, z, hy, hz, hn, ?_⟩
  rw [halign, hnormed]
  exact hspec

theorem aa_budget_scale_ge_one (r p : ℝ) (hr : 0 < r) (hp : p ≤ 1)
    (hlower : 1 / r ^ 2 ≤ p) : 1 ≤ r := by
  have hsq : 1 ≤ r ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hr)).mp (hlower.trans hp)
    simpa using! h
  exact (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hr.le).mp (by simpa using! hsq)

theorem aa_ceil_window_bounds (r : ℝ) (hr : 1 ≤ r) :
    0 < Nat.ceil r ∧ r ≤ (Nat.ceil r : ℝ) ∧
    (((Nat.ceil r : ℝ) + 1) / 2 ≤ (3 / 2 : ℝ) * r) ∧
    (2 * (Nat.ceil r : ℝ) - 1 ≤ 3 * r) := by
  have hceil := Nat.le_ceil r
  have hceilUpper := Nat.ceil_lt_add_one (show 0 ≤ r by linarith)
  have hposR : (0 : ℝ) < Nat.ceil r := by linarith
  exact ⟨by exact_mod_cast hposR, hceil, by linarith, by linarith⟩

theorem prepared_aa_known_window_bounds (A : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (zero : H) (S : Finset H)
    (r : ℝ) (hr : 0 < r)
    (hp : 1 / r ^ 2 ≤ MeasureProb (preparedAAState A zero) S) :
    0 < Nat.ceil r ∧ r ≤ (Nat.ceil r : ℝ) ∧
    (((Nat.ceil r : ℝ) + 1) / 2 ≤ (3 / 2 : ℝ) * r) ∧
    (2 * (Nat.ceil r : ℝ) - 1 ≤ 3 * r) := by
  apply aa_ceil_window_bounds r
  exact aa_budget_scale_ge_one r _ hr
    (measureProb_le_one (prepared_aa_reflection_and_access A zero S hA).2.1 S) hp

theorem counted_blockEncoding_randomized_amplification
    {I D : Type} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
    (target : Matrix D I ℂ) (O B : Matrix H H ℂ) (cs : List (AdjointStep H))
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (hcs : WellFormedAdjointCircuit cs)
    (L : Matrix H D ℂ) (R : Matrix H I ℂ) (scale error η : ℝ)
    (henc : BlockEncoding target (evaluate O cs) L R scale error)
    (zero : H) (S : Finset H) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S)
    (hη : 0 < η) (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖) (herror : error ≤ η / 2)
    (m : ℕ) [NeZero m] (hwindow : 2 * scale / η ≤ (m : ℝ)) :
    let A := evaluatePrepared O B (preparedTrial cs)
    let hA := (preparedTrial_valid hcs).evaluate_unitary hO hB
    ENNReal.ofReal (1 / 8 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (preparedInputQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal (((m : ℝ) + 1) / 2) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (preparedDataQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (adjointQueryCount cs : ℝ)) ∧
    (∀ k, PreparedCircuitValid (countedAAWord (preparedTrial cs) zero S k) ∧
      ApplyGate (evaluatePrepared O B (countedAAWord (preparedTrial cs) zero S k)) (Ket zero) =
        Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
    (∀ k, 0 < MeasureProb (Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) S →
      ∃ (y : QState D) (z : ℂ),
        ConditionalState (Lᴴ *ᵥ Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) = some y ∧
        ‖z‖ = 1 ∧ Normalized y ∧
        IsNormalizedApplication target ψ ((star z) • y)
          (2 * error / ‖stateVector (target *ᵥ ψ)‖)) := by
  (try dsimp only)
  have hA := (preparedTrial_valid hcs).evaluate_unitary hO hB
  refine ⟨?_, randomizedAAHerald_input_cost O B cs zero S hA m,
    randomizedAAHerald_data_cost O B cs zero S hA m, ?_, ?_⟩
  · simpa only [evaluate_preparedTrial] using!
      blockEncoding_randomized_success target (evaluate O cs) B L R scale error η henc hB
        zero S ψ hψ hprepare hproject hη htarget herror m hwindow
  · intro k
    exact ⟨countedAAWord_valid _ zero S k (preparedTrial_valid hcs),
      countedAAWord_run O B _ zero S k hA⟩
  · intro k hk
    rw [evaluate_preparedTrial] at hk ⊢
    apply blockEncoding_randomized_output target (evaluate O cs) B L R scale error
      henc hB zero S ψ hψ hprepare hproject _ k hk
    linarith

theorem outer_randomized_success_of_residue_bounds
    {J W I D : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
    (j₀ : J) (target : Matrix D I ℂ) (samples : J → Matrix D I ℂ)
    (U : J → Matrix W W ℂ) (L : Matrix W D ℂ) (R : Matrix W I ℂ)
    (c : J → ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (samples j) (U j) L R (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α))
    (contour auxiliary tail : Matrix D I ℂ)
    (hidentity : target - (∑ j, c j • samples j) = contour - auxiliary - tail)
    (εIR εAE εTR : ℝ)
    (hIR : ‖contour‖ ≤ εIR) (hAE : ‖auxiliary‖ ≤ εAE) (hTR : ‖tail‖ ≤ εTR)
    (B : Matrix (J × W) (J × W) ℂ) (hB : B ∈ Matrix.unitaryGroup (J × W) ℂ)
    (zero : J × W) (S : Finset (J × W)) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = tagFrame j₀ R *ᵥ ψ)
    (hproject : rangeProjector (tagFrame j₀ L) = Projector S)
    (η : ℝ) (hη : 0 < η) (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖)
    (herror : (∑ j, ‖c j‖ * ε j) + εIR + εAE + εTR ≤ η / 2)
    (m : ℕ) [NeZero m] (hwindow : 2 * (∑ j, ‖c j‖ * α j) / η ≤ (m : ℝ)) :
    ∃ hV : coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀ ∈
        Matrix.unitaryGroup (J × W) ℂ,
      ENNReal.ofReal (1 / 8 : ℝ) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (randomizedAAHerald
          (coefficientLCUUnitary (scaledLCUCoefficients c α) U j₀ * B)
          ((Matrix.unitaryGroup (J × W) ℂ).mul_mem hV hB) zero S m)
        (fun x => x.2 = true) := by
  have houter := outer_blockEncoding_of_residue_bounds j₀ target samples U L R c α ε
    henc hmass contour auxiliary tail hidentity εIR εAE εTR hIR hAE hTR
  refine ⟨houter.unitary, ?_⟩
  exact blockEncoding_randomized_success target _ B _ _ _ _ η houter hB zero S ψ hψ
    hprepare hproject hη htarget herror m hwindow

theorem randomizedAAHerald_support_success (A : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (zero : H) (S : Finset H)
    (m : ℕ) [NeZero m] (choice : Bool × Fin m)
    (hsupport : (choice, true) ∈ (randomizedAAHerald A hA zero S m).support) :
    0 < MeasureProb
      (Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) S := by
  obtain ⟨c, _, hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsupport
  obtain ⟨b, hb, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  have hcEq : c = choice := congrArg Prod.fst heq
  have hbEq : b = true := congrArg Prod.snd heq
  subst c
  subst b
  have hmass : 0 < ProjectiveBranchMass (Projector S) true
      (Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) := by
    apply ENNReal.ofReal_pos.mp
    apply pos_iff_ne_zero.mpr
    exact hb
  have heqMass : ProjectiveBranchMass (Projector S) true
      (Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) =
      MeasureProb
        (Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) S :=
    sum_normSq_collapse _ _
  exact heqMass ▸ hmass

theorem blockEncoding_randomized_supported_output
    {I D : Type} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
    (target : Matrix D I ℂ) (V B : Matrix H H ℂ)
    (L : Matrix H D ℂ) (R : Matrix H I ℂ) (scale error : ℝ)
    (henc : BlockEncoding target V L R scale error) (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (zero : H) (S : Finset H) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S)
    (hgap : error < ‖stateVector (target *ᵥ ψ)‖) (m : ℕ) [NeZero m]
    (choice : Bool × Fin m)
    (hsupport : (choice, true) ∈ (randomizedAAHerald (V * B)
      ((Matrix.unitaryGroup H ℂ).mul_mem henc.unitary hB) zero S m).support) :
    ∃ (y : QState D) (z : ℂ),
      ConditionalState (Lᴴ *ᵥ Run (preparedMark S)
        (preparedAACircuit (V * B) zero (aaRounds choice)) (Ket zero)) = some y ∧
      ‖z‖ = 1 ∧ Normalized y ∧
      IsNormalizedApplication target ψ ((star z) • y)
        (2 * error / ‖stateVector (target *ᵥ ψ)‖) := by
  apply blockEncoding_randomized_output target V B L R scale error henc hB zero S ψ hψ
    hprepare hproject hgap
  exact randomizedAAHerald_support_success _ _ zero S m choice hsupport

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
