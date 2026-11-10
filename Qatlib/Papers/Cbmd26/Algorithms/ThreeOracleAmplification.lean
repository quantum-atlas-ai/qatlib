/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CleanTwoOracleWord
import Qatlib.Papers.Cbmd26.Algorithms.CountedAmplificationBridge
set_option warningAsError false

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
open scoped Matrix.Norms.L2Operator ENNReal

inductive ThreeOracleStep (H : Type*) where
  | matrixStep : PreparedStep H → ThreeOracleStep H
  | stateForward : ThreeOracleStep H
  | stateBackward : ThreeOracleStep H

def threeFirstQueries {H : Type*} : List (ThreeOracleStep H) → ℕ
  | [] => 0
  | .matrixStep c :: cs => preparedDataQueries [c] + threeFirstQueries cs
  | _ :: cs => threeFirstQueries cs

def threeSecondQueries {H : Type*} : List (ThreeOracleStep H) → ℕ
  | [] => 0
  | .matrixStep c :: cs => preparedInputQueries [c] + threeSecondQueries cs
  | _ :: cs => threeSecondQueries cs

def threeStateQueries {H : Type*} : List (ThreeOracleStep H) → ℕ
  | [] => 0
  | .matrixStep _ :: cs => threeStateQueries cs
  | _ :: cs => threeStateQueries cs + 1

def threeFixedGates {H : Type*} : List (ThreeOracleStep H) → ℕ
  | [] => 0
  | .matrixStep c :: cs => preparedFixedGates [c] + threeFixedGates cs
  | _ :: cs => threeFixedGates cs

theorem three_counts_append {H : Type*} (cs ds : List (ThreeOracleStep H)) :
    threeFirstQueries (cs ++ ds) = threeFirstQueries cs + threeFirstQueries ds ∧
    threeSecondQueries (cs ++ ds) = threeSecondQueries cs + threeSecondQueries ds ∧
    threeStateQueries (cs ++ ds) = threeStateQueries cs + threeStateQueries ds ∧
    threeFixedGates (cs ++ ds) = threeFixedGates cs + threeFixedGates ds := by
  induction cs with
  | nil => simp [threeFirstQueries, threeSecondQueries, threeStateQueries, threeFixedGates]
  | cons c cs ih =>
    cases c <;> simp [threeFirstQueries, threeSecondQueries, threeStateQueries, threeFixedGates,
      ih.1, ih.2.1, ih.2.2.1, ih.2.2.2, Nat.add_assoc, Nat.add_comm 1]

theorem three_matrix_counts {H : Type*} (cs : List (PreparedStep H)) :
    threeFirstQueries (cs.map ThreeOracleStep.matrixStep) = preparedDataQueries cs ∧
    threeSecondQueries (cs.map ThreeOracleStep.matrixStep) = preparedInputQueries cs ∧
    threeStateQueries (cs.map ThreeOracleStep.matrixStep) = 0 ∧
    threeFixedGates (cs.map ThreeOracleStep.matrixStep) = preparedFixedGates cs := by
  induction cs with
  | nil => simp [threeFirstQueries, threeSecondQueries, threeStateQueries, threeFixedGates,
      preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | cons c cs ih =>
    cases c <;> simp [threeFirstQueries, threeSecondQueries, threeStateQueries, threeFixedGates,
      preparedDataQueries, preparedInputQueries, preparedFixedGates,
      ih.1, ih.2.1, ih.2.2.1, ih.2.2.2, Nat.add_comm 1]

def expandThreeOracleWord {H : Type*} (body : List (PreparedStep H)) :
    List (PreparedStep H) → List (ThreeOracleStep H)
  | [] => []
  | .gate V :: cs => .matrixStep (.gate V) :: expandThreeOracleWord body cs
  | .dataForward :: cs => body.map ThreeOracleStep.matrixStep ++ expandThreeOracleWord body cs
  | .dataBackward :: cs => (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord body).map ThreeOracleStep.matrixStep ++
      expandThreeOracleWord body cs
  | .prepareForward :: cs => .stateForward :: expandThreeOracleWord body cs
  | .prepareBackward :: cs => .stateBackward :: expandThreeOracleWord body cs

theorem expandThreeOracleWord_counts {H : Type*}
    (body program : List (PreparedStep H)) :
    threeFirstQueries (expandThreeOracleWord body program) =
      preparedDataQueries program * preparedDataQueries body ∧
    threeSecondQueries (expandThreeOracleWord body program) =
      preparedDataQueries program * preparedInputQueries body ∧
    threeStateQueries (expandThreeOracleWord body program) = preparedInputQueries program ∧
    threeFixedGates (expandThreeOracleWord body program) =
      preparedFixedGates program + preparedDataQueries program * preparedFixedGates body := by
  induction program with
  | nil => simp [expandThreeOracleWord, threeFirstQueries, threeSecondQueries,
      threeStateQueries, threeFixedGates, preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | cons c cs ih =>
    have hm := three_matrix_counts body
    have hi :=
        three_matrix_counts (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord body)
    have hinv := Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_counts body
    cases c <;> simp [expandThreeOracleWord, (three_counts_append _ _).1,
      (three_counts_append _ _).2.1, (three_counts_append _ _).2.2.1,
      (three_counts_append _ _).2.2.2, threeFirstQueries, threeSecondQueries,
      threeStateQueries, threeFixedGates, preparedDataQueries, preparedInputQueries,
      preparedFixedGates, ih.1, ih.2.1, ih.2.2.1, ih.2.2.2,
      hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2,
      hinv.1, hinv.2.1, hinv.2.2, Nat.add_mul] <;> omega

variable {H : Type} [Fintype H] [DecidableEq H]

def threeInstruction (O1 O2 B : Matrix H H ℂ) : ThreeOracleStep H → Matrix H H ℂ
  | .matrixStep c => preparedInstruction O1 O2 c
  | .stateForward => B
  | .stateBackward => Bᴴ

def evaluateThree (O1 O2 B : Matrix H H ℂ) : List (ThreeOracleStep H) → Matrix H H ℂ
  | [] => 1
  | c :: cs => threeInstruction O1 O2 B c * evaluateThree O1 O2 B cs

def ThreeInstructionValid : ThreeOracleStep H → Prop
  | .matrixStep c => PreparedInstructionValid c
  | _ => True

def ThreeCircuitValid (cs : List (ThreeOracleStep H)) : Prop :=
  ∀ c ∈ cs, ThreeInstructionValid c

theorem evaluateThree_append (O1 O2 B : Matrix H H ℂ) (cs ds : List (ThreeOracleStep H)) :
    evaluateThree O1 O2 B (cs ++ ds) = evaluateThree O1 O2 B cs * evaluateThree O1 O2 B ds := by
  induction cs with
  | nil => simp [evaluateThree]
  | cons c cs ih => simp [evaluateThree, ih, Matrix.mul_assoc]

theorem evaluateThree_matrix (O1 O2 B : Matrix H H ℂ) (cs : List (PreparedStep H)) :
    evaluateThree O1 O2 B (cs.map ThreeOracleStep.matrixStep) = evaluatePrepared O1 O2 cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [evaluateThree, threeInstruction, evaluatePrepared, ih]

theorem expandThreeOracleWord_evaluate (O1 O2 B : Matrix H H ℂ)
    (body program : List (PreparedStep H)) :
    evaluateThree O1 O2 B (expandThreeOracleWord body program) =
      evaluatePrepared (evaluatePrepared O1 O2 body) B program := by
  induction program with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [expandThreeOracleWord, evaluateThree_append,
      evaluateThree_matrix, evaluateThree, threeInstruction, evaluatePrepared,
      preparedInstruction, Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_evaluate, ih]

theorem expandThreeOracleWord_valid {body program : List (PreparedStep H)}
    (hb : PreparedCircuitValid body) (hp : PreparedCircuitValid program) :
    ThreeCircuitValid (expandThreeOracleWord body program) := by
  have hm (cs : List (PreparedStep H)) (hc : PreparedCircuitValid cs) :
      ThreeCircuitValid (cs.map ThreeOracleStep.matrixStep) := by
    intro c h
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    exact hc d hd
  induction program with
  | nil => simp [expandThreeOracleWord, ThreeCircuitValid]
  | cons c cs ih =>
    have ht := ih (fun d hd => hp d (List.mem_cons_of_mem c hd))
    cases c with
    | gate V =>
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hp (.gate V) (by simp)
      · exact ht d hd
    | dataForward =>
      intro d hd
      exact (List.mem_append.mp hd).elim (hm body hb d) (ht d)
    | dataBackward =>
      intro d hd
      exact (List.mem_append.mp hd).elim
        (hm _ (Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_valid hb) d) (ht d)
    | prepareForward | prepareBackward =>
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · trivial
      · exact ht d hd

theorem ThreeCircuitValid.evaluate_unitary {cs : List (ThreeOracleStep H)}
    (hcs : ThreeCircuitValid cs) {O1 O2 B : Matrix H H ℂ}
    (hO1 : O1 ∈ Matrix.unitaryGroup H ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup H ℂ)
    (hB : B ∈ Matrix.unitaryGroup H ℂ) :
    evaluateThree O1 O2 B cs ∈ Matrix.unitaryGroup H ℂ := by
  induction cs with
  | nil => exact (Matrix.unitaryGroup H ℂ).one_mem
  | cons c cs ih =>
    apply (Matrix.unitaryGroup H ℂ).mul_mem _ (ih (fun d hd => hcs d (List.mem_cons_of_mem c hd)))
    have hc := hcs c (by simp)
    cases c with
    | matrixStep d => exact preparedInstruction_unitary hO1 hO2 hc
    | stateForward => exact hB
    | stateBackward => exact adjoint_unitary hB

def threeAAWord (body : List (PreparedStep H)) (zero : H) (S : Finset H) (k : ℕ) :
    List (ThreeOracleStep H) :=
  expandThreeOracleWord body (countedAAWord [.dataForward, .prepareForward] zero S k)

theorem threeAAWord_counts (body : List (PreparedStep H)) (zero : H) (S : Finset H) (k : ℕ) :
    threeFirstQueries (threeAAWord body zero S k) = (2 * k + 1) * preparedDataQueries body ∧
    threeSecondQueries (threeAAWord body zero S k) = (2 * k + 1) * preparedInputQueries body ∧
    threeStateQueries (threeAAWord body zero S k) = 2 * k + 1 ∧
    threeFixedGates (threeAAWord body zero S k) =
      (2 * k + 1) * preparedFixedGates body + 2 * k := by
  have h := expandThreeOracleWord_counts body
    (countedAAWord [.dataForward, .prepareForward] zero S k)
  have hc := countedAAWord_counts ([.dataForward, .prepareForward] : List (PreparedStep H)) zero S k
  simp only [preparedDataQueries, preparedInputQueries, preparedFixedGates,
    Nat.zero_add, Nat.mul_one, Nat.mul_zero] at hc
  simpa only [threeAAWord, hc.1, hc.2.1, hc.2.2, Nat.add_comm] using h

theorem threeAAWord_valid (body : List (PreparedStep H)) (zero : H) (S : Finset H) (k : ℕ)
    (hb : PreparedCircuitValid body) : ThreeCircuitValid (threeAAWord body zero S k) := by
  apply expandThreeOracleWord_valid hb
  apply countedAAWord_valid
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> trivial

theorem threeAAWord_run (O1 O2 B : Matrix H H ℂ) (body : List (PreparedStep H))
    (zero : H) (S : Finset H) (k : ℕ)
    (hA : evaluatePrepared O1 O2 body * B ∈ Matrix.unitaryGroup H ℂ) :
    ApplyGate (evaluateThree O1 O2 B (threeAAWord body zero S k)) (Ket zero) =
      Run (preparedMark S) (preparedAACircuit (evaluatePrepared O1 O2 body * B) zero k) (Ket zero) := by
  rw [threeAAWord, expandThreeOracleWord_evaluate]
  simpa only [evaluatePrepared, preparedInstruction, Matrix.mul_one] using
    countedAAWord_run (evaluatePrepared O1 O2 body) B
      [.dataForward, .prepareForward] zero S k (by simpa only
        [evaluatePrepared, preparedInstruction, Matrix.mul_one] using hA)

theorem three_randomized_repetition_cost (A : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (zero : H) (S : Finset H)
    (m : ℕ) [NeZero m] (q : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (((2 * aaRounds x.1 + 1) * q : ℕ) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (q : ℝ)) := by
  rw [randomizedAAHerald_schedule_observable A hA zero S m
    (fun c => (((2 * aaRounds c + 1) * q : ℕ) : ℝ≥0∞))]
  have hcast (k : ℕ) : (((2 * k + 1) * q : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((2 * (k : ℝ) + 1) * (q : ℝ)) := by norm_cast
  simp_rw [hcast]
  rw [aaSchedule_expectation m (fun k => (2 * (k : ℝ) + 1) * (q : ℝ))
    (fun k => by positivity), ← Finset.sum_mul, Qatlib.Papers.Cbmd26.Algorithms.CBMD.sum_odd_indices]
  congr 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp
  ring

theorem threeAAWord_expected_costs (A : Matrix H H ℂ)
    (hA : A ∈ Matrix.unitaryGroup H ℂ) (body : List (PreparedStep H))
    (zero : H) (S : Finset H) (m : ℕ) [NeZero m] :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeFirstQueries (threeAAWord body zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (preparedDataQueries body : ℝ)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeSecondQueries (threeAAWord body zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (preparedInputQueries body : ℝ)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeStateQueries (threeAAWord body zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal (((m : ℝ) + 1) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [(threeAAWord_counts body zero S _).1]
    exact three_randomized_repetition_cost A hA zero S m _
  · simp_rw [(threeAAWord_counts body zero S _).2.1]
    exact three_randomized_repetition_cost A hA zero S m _
  · simp_rw [(threeAAWord_counts body zero S _).2.2.1]
    simpa only [Nat.mul_one, Nat.cast_one, mul_one] using
      three_randomized_repetition_cost A hA zero S m 1

theorem threeAAWord_path_budget (body : List (PreparedStep H))
    (zero : H) (S : Finset H) (m : ℕ) [NeZero m] (choice : Bool × Fin m) :
    threeFirstQueries (threeAAWord body zero S (aaRounds choice)) ≤
      (2 * m - 1) * preparedDataQueries body ∧
    threeSecondQueries (threeAAWord body zero S (aaRounds choice)) ≤
      (2 * m - 1) * preparedInputQueries body ∧
    threeStateQueries (threeAAWord body zero S (aaRounds choice)) ≤ 2 * m - 1 := by
  have hk : aaRounds choice < m := by
    unfold aaRounds
    split_ifs
    · exact choice.2.isLt
    · exact Nat.pos_of_ne_zero (NeZero.ne m)
  have hcount : 2 * aaRounds choice + 1 ≤ 2 * m - 1 := by omega
  rw [(threeAAWord_counts body zero S _).1, (threeAAWord_counts body zero S _).2.1,
    (threeAAWord_counts body zero S _).2.2.1]
  exact ⟨Nat.mul_le_mul_right _ hcount, Nat.mul_le_mul_right _ hcount, hcount⟩

theorem three_oracle_blockEncoding_amplification
    {I D : Type} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
    (target : Matrix D I ℂ) (O1 O2 B : Matrix H H ℂ)
    (body : List (PreparedStep H)) (hbody : PreparedCircuitValid body)
    (hO1 : O1 ∈ Matrix.unitaryGroup H ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup H ℂ)
    (hB : B ∈ Matrix.unitaryGroup H ℂ)
    (L : Matrix H D ℂ) (R : Matrix H I ℂ) (scale error η : ℝ)
    (henc : BlockEncoding target (evaluatePrepared O1 O2 body) L R scale error)
    (zero : H) (S : Finset H) (ψ : QState I) (hψ : Normalized ψ)
    (hprepare : ApplyGate B (Ket zero) = R *ᵥ ψ)
    (hproject : rangeProjector L = Projector S)
    (hη : 0 < η) (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖) (herror : error ≤ η / 2)
    (m : ℕ) [NeZero m] (hwindow : 2 * scale / η ≤ (m : ℝ)) :
    let A := evaluatePrepared O1 O2 body * B
    let hA := (Matrix.unitaryGroup H ℂ).mul_mem (hbody.evaluate_unitary hO1 hO2) hB
    ENNReal.ofReal (1/8 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeFirstQueries (threeAAWord body zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (preparedDataQueries body : ℝ)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeSecondQueries (threeAAWord body zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal ((((m : ℝ) + 1) / 2) * (preparedInputQueries body : ℝ)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeStateQueries (threeAAWord body zero S (aaRounds x.1)) : ℝ≥0∞)) =
      ENNReal.ofReal (((m : ℝ) + 1) / 2) ∧
    (∀ k, ThreeCircuitValid (threeAAWord body zero S k) ∧
      ApplyGate (evaluateThree O1 O2 B (threeAAWord body zero S k)) (Ket zero) =
        Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
    (∀ choice : Bool × Fin m,
      (choice, true) ∈ (randomizedAAHerald A hA zero S m).support →
      ∃ (y : QState D) (z : ℂ),
        ConditionalState (Lᴴ *ᵥ Run (preparedMark S)
          (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) = some y ∧
        ‖z‖ = 1 ∧ Normalized y ∧
        IsNormalizedApplication target ψ ((star z) • y)
          (2 * error / ‖stateVector (target *ᵥ ψ)‖)) := by
  (try dsimp only)
  have hA := (Matrix.unitaryGroup H ℂ).mul_mem (hbody.evaluate_unitary hO1 hO2) hB
  have hc := threeAAWord_expected_costs (evaluatePrepared O1 O2 body * B) hA body zero S m
  refine ⟨?_, hc.1, hc.2.1, hc.2.2, ?_, ?_⟩
  · exact blockEncoding_randomized_success target (evaluatePrepared O1 O2 body) B L R
      scale error η henc hB zero S ψ hψ hprepare hproject hη htarget herror m hwindow
  · intro k
    exact ⟨threeAAWord_valid body zero S k hbody, threeAAWord_run O1 O2 B body zero S k hA⟩
  · intro choice hs
    exact blockEncoding_randomized_supported_output target (evaluatePrepared O1 O2 body) B L R
      scale error henc hB zero S ψ hψ hprepare hproject (by linarith) m choice hs

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
