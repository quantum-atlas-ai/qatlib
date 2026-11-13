/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeDefs

/-!
# Coherent variable-time evolution and cost bounds

This module proves the execution semantics and stopped-history invariants of
`CoherentVtFrame.coherentProgram`. It develops fresh stopping-mass accounting, paid-word and
macro cost identities, amplification gain windows, and second-moment estimates for fixed and
policy-selected schedules. `sourceTheorem1_measured` combines a conditional equation (6) access
bound with the explicit tight access-cost formula.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `CoherentVtFrame.coherentProgram_run_eq`: agreement with stage evolution.
* `CoherentVtFrame.freshStopMass_sum`: fresh stopping-mass accounting.
* `CoherentVtFrame.coherentVtProgram_accessTime_eq_chargedAccessTime`: measured access cost.
* `sourceTheorem1_measured`: conditional source bound and tight-cost identity.
* `CoherentVtFrame.amplifiedSecondMoment_le_bound`: scheduled second-moment estimate.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVtFrame

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Matrix
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators

variable {H : Type} [Fintype H] [DecidableEq H]
variable {m : ℕ}

namespace CoherentVtFrame

/-- The circuit obtained by applying the frame's stage operators in increasing stage order. -/
def coherentProgram (f : CoherentVtFrame H m) : Circuit H :=
  (List.finRange m).map fun j => Step.gate (f.stageOp j)

/-- Every gate of the frame's coherent program is unitary. -/
theorem coherentProgram_unitary (f : CoherentVtFrame H m) :
    IsUnitaryCircuit (f.coherentProgram) := by
  intro U hU
  have hU' : ∃ a ∈ List.finRange m, Step.gate (f.stageOp a) = Step.gate U := by
    simpa only [coherentProgram, List.mem_map] using! hU
  obtain ⟨j, _, hj⟩ := hU'
  have hj' : f.stageOp j = U := by simpa only [Step.gate.injEq] using! hj
  rw [← hj']
  exact f.stageOp_unitary j

/-- The total matrix of a gate list in execution order, with later gates multiplying on the
left. -/
def listTotalOp (C : List (Matrix H H ℂ)) : Matrix H H ℂ :=
  C.foldr (fun U A => A * U) 1

/-- The total matrix obtained by composing all stage operators of the frame in execution order. -/
def totalOp (f : CoherentVtFrame H m) : Matrix H H ℂ :=
  listTotalOp ((List.finRange m).map (f.stageOp))

/-- Applying the total matrix of a list equals successively applying its gate matrices to the
input state. -/
private theorem listTotalOp_apply {C : List (Matrix H H ℂ)} (ψ : QState H) :
    ApplyGate (listTotalOp C) ψ = C.foldl (fun s U => ApplyGate U s) ψ := by
  induction C generalizing ψ with
  | nil => simp [listTotalOp, applyGate_one]
  | cons U C ih =>
    have hform : listTotalOp (U :: C) = listTotalOp C * U := by
      simp only [listTotalOp, List.foldr_cons]
    rw [hform, applyGate_mul, ih]
    rfl

/-- The total matrix of a list of unitary matrices is unitary. -/
theorem listTotalOp_unitary {C : List (Matrix H H ℂ)} :
    (∀ U ∈ C, U ∈ Matrix.unitaryGroup H ℂ) → listTotalOp C ∈ Matrix.unitaryGroup H ℂ := by
  induction C with
  | nil =>
      intro h
      simp [listTotalOp]
  | cons U C ih =>
      intro h
      simp only [listTotalOp, List.foldr_cons]
      refine unitary_mul (ih ?_) ?_
      · intro V hV
        exact h V (List.Mem.tail U hV)
      · exact h U List.mem_cons_self

/-- The total evolution matrix of a coherent variable-time frame is unitary. -/
theorem totalOp_unitary (f : CoherentVtFrame H m) :
    f.totalOp ∈ Matrix.unitaryGroup H ℂ := by
  apply listTotalOp_unitary
  intro U hU
  simp only [List.mem_map] at hU
  obtain ⟨j, _, hj⟩ := hU
  rw [← hj]
  exact f.stageOp_unitary j

/-- Projecting onto the previously stopped subspace after the current stage equals the stopped
projector itself. -/
theorem stop_mul_stageOp (f : CoherentVtFrame H m) (j : Fin m) :
    f.stopAt j * f.stageOp j = f.stopAt j := by
  have hid : f.stopAt j * f.stopAt j = f.stopAt j :=
    (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).1
  have hz : f.stopAt j * (1 - f.stopAt j) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hid]
    simp
  simp only [CoherentVtFrame.stageOp, coherentStage]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hz, Matrix.zero_mul, hid, _root_.add_zero]

/-- The next stopped-history projector is the sum of the previous stopped projector and the
fresh stopping projector. -/
theorem stopHistory_split (f : CoherentVtFrame H m) (j : Fin m) :
    f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ = f.stopAt j + f.freshStop j := by
  simp only [freshStop]
  abel

/-- The component outside the next stopped subspace evolves under the stage operator exactly as
under the underlying round matrix. -/
theorem runningPart_step (f : CoherentVtFrame H m) (j : Fin m) :
    (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stageOp j
      = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.round j := by
  have hle : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  have hnest : (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stopAt j = f.stopAt j :=
    nestedStopFamily_mul_rev f.stopNested hle
  have hzero1 : (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stopAt j = 0 := by
    calc
      (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stopAt j
          = 1 * f.stopAt j - (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stopAt j :=
            Matrix.sub_mul _ _ _
      _ = f.stopAt j - f.stopAt j := by rw [Matrix.one_mul, hnest]
      _ = 0 := by simp
  have hzero2 : (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * (1 - f.stopAt j)
      = 1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    calc
      (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * (1 - f.stopAt j)
          = (1 * (1 - f.stopAt j)
              - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ * (1 - f.stopAt j)) := Matrix.sub_mul _ _ _
      _ = ((1 - f.stopAt j)
              - (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ * 1
                  - (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stopAt j)) := by
            rw [Matrix.one_mul, Matrix.mul_sub]
      _ = ((1 - f.stopAt j)
              - (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ - f.stopAt j)) := by
            rw [Matrix.mul_one, hnest]
      _ = 1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by module
  calc
    (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stageOp j
        = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
            * (f.stopAt j + (1 - f.stopAt j) * f.round j) := by
          show (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
              * (f.stopAt j + (1 - f.stopAt j) * f.round j)
              = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                  * (f.stopAt j + (1 - f.stopAt j) * f.round j)
          rfl
    _ = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stopAt j
            + (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                * (1 - f.stopAt j) * f.round j := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc]
    _ = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.round j := by
          rw [hzero1, _root_.zero_add, hzero2]

/-- The zero-stage prefix state equals the input state. -/
theorem stageState_zero (f : CoherentVtFrame H m) (ψ : QState H) (h : 0 ≤ m) :
    f.stageState ψ 0 h = ψ := rfl

/-- The state at prefix `n + 1` is obtained by applying stage `n` to the state at prefix `n`. -/
theorem stageState_succ (f : CoherentVtFrame H m) (ψ : QState H) (n : ℕ) (h : n + 1 ≤ m) :
    f.stageState ψ (n + 1) h
      = ApplyGate (f.stageOp ⟨n, Nat.lt_of_succ_le h⟩)
          (f.stageState ψ n (Nat.le_of_succ_le h)) := rfl

/-- The measurement masses of the projections onto an orthogonal projector and its complement
sum to the input state's total mass. -/
private theorem projective_complement {P : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (ψ : QState H) :
    MeasureProb (ApplyGate (1 - P) ψ) Finset.univ
      + MeasureProb (ApplyGate P ψ) Finset.univ
      = MeasureProb ψ Finset.univ := by
  have h := projectiveBranchMass_add hP ψ
  simpa [ProjectiveBranchMass, ProjectiveBranch] using! h

/-- The total mass of the fresh stopped projection after applying round `j` to the pre-stage
prefix state. -/
def freshStopMass (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : ℝ :=
  MeasureProb
    (ApplyGate (f.freshStop j) (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))))
    Finset.univ

/-- Fresh stopping mass at every stage is nonnegative. -/
theorem freshStopMass_nonneg (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    0 ≤ f.freshStopMass ψ j := measureProb_nonneg _ _

/-- Stopped mass after a stage equals the previous stopped mass plus the fresh stopping mass at
that stage. -/
theorem stoppedMass_succ (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    f.stoppedMass ψ (j.val + 1) (by omega) = f.stoppedMass ψ j.val (by omega)
      + f.freshStopMass ψ j := by
  have hstep : f.stageState ψ (j.val + 1) (by omega)
      = ApplyGate (f.stageOp j) (f.stageState ψ j.val (by omega)) := by
    have h := f.stageState_succ ψ j.val (by omega)
    have hfin : (⟨j.val, Nat.lt_of_succ_le (by omega)⟩ : Fin m) = j := Fin.ext rfl
    rw [hfin] at h
    exact h
  have horth : IsOrthogonalProjector (f.freshStop j) := f.freshStop_orth j
  have hFP : f.freshStop j * f.stopAt j = 0 := (f.freshStop_orthogonal j).2
  have hidem : f.stopAt j * f.stopAt j = f.stopAt j :=
    (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).1
  have hcompl : f.freshStop j * (1 - f.stopAt j) = f.freshStop j := by
    calc
      f.freshStop j * (1 - f.stopAt j)
          = f.freshStop j * 1 - f.freshStop j * f.stopAt j := Matrix.mul_sub _ _ _
      _ = f.freshStop j - 0 := by rw [Matrix.mul_one, hFP]
      _ = f.freshStop j := by rw [sub_zero]
  have hcomplP : (1 - f.stopAt j) * f.stopAt j = 0 := by
    calc
      (1 - f.stopAt j) * f.stopAt j
          = 1 * f.stopAt j - f.stopAt j * f.stopAt j := Matrix.sub_mul _ _ _
      _ = f.stopAt j - f.stopAt j := by rw [Matrix.one_mul, hidem]
      _ = 0 := by simp
  have hcomplP2 : (1 - f.stopAt j) * (1 - f.stopAt j) = 1 - f.stopAt j := by
    calc
      (1 - f.stopAt j) * (1 - f.stopAt j)
          = (1 - f.stopAt j) * 1 - (1 - f.stopAt j) * f.stopAt j := Matrix.mul_sub _ _ _
      _ = (1 - f.stopAt j) - 0 := by rw [Matrix.mul_one, hcomplP]
      _ = 1 - f.stopAt j := by rw [sub_zero]
  have hrunning : (1 - f.stopAt j) * f.stageOp j = (1 - f.stopAt j) * f.round j := by
    simp only [CoherentVtFrame.stageOp, coherentStage]
    rw [Matrix.mul_add, hcomplP, _root_.zero_add, ← Matrix.mul_assoc, hcomplP2]
  have hreach : f.stopAt j * f.stageOp j = f.stopAt j := f.stop_mul_stageOp j

  have hmat1 : (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.round j
      = (1 - f.freshStop j) * (1 - f.stopAt j) * f.round j := by
    have hsplit : f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
        = f.stopAt j + f.freshStop j := f.stopHistory_split j
    have hsub : 1 - (f.stopAt j + f.freshStop j)
        = (1 - f.stopAt j) - f.freshStop j := by abel
    have h2 : (1 - f.freshStop j) * (1 - f.stopAt j)
        = (1 - f.stopAt j) - f.freshStop j := by
      calc
        (1 - f.freshStop j) * (1 - f.stopAt j)
            = (1 - f.freshStop j) * 1 - (1 - f.freshStop j) * f.stopAt j :=
              Matrix.mul_sub _ _ _
        _ = (1 - f.freshStop j) - (f.stopAt j - f.freshStop j * f.stopAt j) := by
            rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
        _ = (1 - f.freshStop j) - f.stopAt j := by rw [hFP, sub_zero]
        _ = (1 - f.stopAt j) - f.freshStop j := by abel
    rw [hsplit, hsub, h2]

  have hA : MeasureProb (ApplyGate (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      + MeasureProb (ApplyGate (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      = MeasureProb (f.stageState ψ (j.val + 1) (by omega)) Finset.univ :=
    projective_complement (f.stopNested.1 (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))
      (f.stageState ψ (j.val + 1) (by omega))
  have hB : MeasureProb (ApplyGate (1 - f.stopAt j)
      (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      + MeasureProb (ApplyGate (f.stopAt j)
        (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      = MeasureProb (f.stageState ψ (j.val + 1) (by omega)) Finset.univ :=
    projective_complement (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
      (f.stageState ψ (j.val + 1) (by omega))
  have hC : MeasureProb (ApplyGate (1 - f.freshStop j)
        (ApplyGate (1 - f.stopAt j)
          (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))))) Finset.univ
      + MeasureProb (ApplyGate (f.freshStop j)
        (ApplyGate (1 - f.stopAt j)
          (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))))) Finset.univ
      = MeasureProb (ApplyGate (1 - f.stopAt j)
        (ApplyGate (f.round j) (f.stageState ψ j.val (by omega)))) Finset.univ :=
    projective_complement horth
      (ApplyGate (1 - f.stopAt j) (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))))

  have hrunning' : MeasureProb (ApplyGate (1 - f.stopAt j)
      (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      = MeasureProb (ApplyGate (1 - f.stopAt j)
        (ApplyGate (f.round j) (f.stageState ψ j.val (by omega)))) Finset.univ := by
    rw [hstep, ← applyGate_mul, hrunning, ← applyGate_mul]
  have hfresh' : MeasureProb (ApplyGate (1 - f.freshStop j)
        (ApplyGate (1 - f.stopAt j)
          (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))))) Finset.univ
      = MeasureProb (ApplyGate (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (f.stageState ψ (j.val + 1) (by omega))) Finset.univ := by
    rw [← applyGate_mul, ← applyGate_mul, hstep, ← applyGate_mul,
      f.runningPart_step j, hmat1]
  have hfresh : MeasureProb (ApplyGate (f.freshStop j)
        (ApplyGate (1 - f.stopAt j)
          (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))))) Finset.univ
      = f.freshStopMass ψ j := by
    rw [← applyGate_mul, hcompl]
    rfl
  have hreach' : MeasureProb (ApplyGate (f.stopAt j)
      (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      = MeasureProb (ApplyGate (f.stopAt j) (f.stageState ψ j.val (by omega))) Finset.univ := by
    rw [hstep, ← applyGate_mul, hreach]
  have hbefore : MeasureProb (ApplyGate (f.stopAt j) (f.stageState ψ j.val (by omega)))
      Finset.univ = f.stoppedMass ψ j.val (by omega) := rfl
  have hafter : MeasureProb (ApplyGate (f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      (f.stageState ψ (j.val + 1) (by omega))) Finset.univ
      = f.stoppedMass ψ (j.val + 1) (by omega) := rfl
  linarith

/-- Stopped mass at the zero-stage prefix is zero. -/
theorem stoppedMass_zero (f : CoherentVtFrame H m) (ψ : QState H) (h : 0 ≤ m) :
    f.stoppedMass ψ 0 h = 0 := by
  have hz : f.stop (0 : Fin (m + 1)) = 0 := f.stopZero
  have hdef : f.stoppedMass ψ 0 h = MeasureProb (ApplyGate (f.stop (0 : Fin (m + 1)))
      (f.stageState ψ 0 h)) Finset.univ := rfl
  rw [hdef, hz]
  simp [ApplyGate, Matrix.mulVec, MeasureProb, BornProb]

/-- Every valid stage prefix preserves the total measurement mass of the input state. -/
theorem stageState_mass (f : CoherentVtFrame H m) (ψ : QState H) {n : ℕ} (hn : n ≤ m) :
    MeasureProb (f.stageState ψ n hn) Finset.univ = MeasureProb ψ Finset.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n + 1 ≤ m := hn
      have hunit : f.stageOp ⟨n, Nat.lt_of_succ_le hn'⟩ ∈ Matrix.unitaryGroup H ℂ :=
        f.stageOp_unitary ⟨n, Nat.lt_of_succ_le hn'⟩
      rw [f.stageState_succ ψ n hn', measureProb_applyGate_univ hunit,
        ih (Nat.le_of_succ_le hn')]

/-- Stopped mass at any valid prefix is bounded by the total mass of the input state. -/
theorem stoppedMass_le_stateMass (f : CoherentVtFrame H m) (ψ : QState H) {n : ℕ}
    (hn : n ≤ m) :
    f.stoppedMass ψ n hn ≤ MeasureProb ψ Finset.univ := by
  have h := projective_complement (f.stopNested.1 ⟨n, Nat.lt_succ_of_le hn⟩)
    (f.stageState ψ n hn)
  have hnonneg : 0 ≤ MeasureProb (ApplyGate (1 - f.stop ⟨n, Nat.lt_succ_of_le hn⟩)
      (f.stageState ψ n hn)) Finset.univ := measureProb_nonneg _ _
  have hmass : MeasureProb (f.stageState ψ n hn) Finset.univ = MeasureProb ψ Finset.univ :=
    f.stageState_mass ψ hn
  rw [stoppedMass, ← hmass]
  linarith

/-- Extends fresh stopping mass to natural indices by assigning zero outside the stage range. -/
def freshStopMassAt (f : CoherentVtFrame H m) (ψ : QState H) (j : ℕ) : ℝ :=
  if hj : j < m then f.freshStopMass ψ ⟨j, hj⟩ else 0

/-- At a valid natural stage index, the extended fresh stopping mass equals the finite-index
fresh stopping mass. -/
theorem freshStopMassAt_of_lt (f : CoherentVtFrame H m) (ψ : QState H) {j : ℕ}
    (hj : j < m) :
    f.freshStopMassAt ψ j = f.freshStopMass ψ ⟨j, hj⟩ := by
  simp [freshStopMassAt, hj]

/-- The sum of fresh stopping masses below a valid prefix length equals the stopped mass at that
prefix. -/
theorem freshStopMass_sum (f : CoherentVtFrame H m) (ψ : QState H) {n : ℕ} (hn : n ≤ m) :
    (∑ j ∈ Finset.range n, f.freshStopMassAt ψ j) = f.stoppedMass ψ n hn := by
  induction n with
  | zero =>
      simp only [Finset.sum_range_zero]
      exact (f.stoppedMass_zero ψ (by omega)).symm
  | succ n ih =>
      have hn' : n + 1 ≤ m := hn
      have hle : n ≤ m := Nat.le_of_succ_le hn
      have hlt : n < m := Nat.lt_of_succ_le hn'
      rw [Finset.sum_range_succ, ih hle]
      have hstep := f.stoppedMass_succ (ψ := ψ) ⟨n, hlt⟩
      rw [hstep, f.freshStopMassAt_of_lt ψ hlt]

/-- The sum of fresh stopping masses over `Fin m` equals the range sum of their natural-index
extension. -/
theorem sum_fin_eq_sum_range (f : CoherentVtFrame H m) (ψ : QState H) :
    (∑ j : Fin m, f.freshStopMass ψ j) = ∑ j ∈ Finset.range m, f.freshStopMassAt ψ j := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hlt : j.val < m := j.isLt
  rw [f.freshStopMassAt_of_lt ψ hlt]

/-- The sum of all fresh stopping masses is bounded by the input state's total measurement mass. -/
theorem freshStopMass_total_le (f : CoherentVtFrame H m) (ψ : QState H) :
    (∑ j : Fin m, f.freshStopMass ψ j) ≤ MeasureProb ψ Finset.univ := by
  have hsum := f.freshStopMass_sum ψ (n := m) (by omega)
  have hfin := f.sum_fin_eq_sum_range ψ
  rw [← hfin] at hsum
  rw [hsum]
  exact f.stoppedMass_le_stateMass ψ (by omega)

/-- For a normalized input and a final stopped projector equal to the identity, fresh stopping
masses sum to one. -/
theorem freshStopMass_total_eq_one (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1)
    (hnorm : Normalized ψ) :
    (∑ j : Fin m, f.freshStopMass ψ j) = 1 := by
  have hsum := f.freshStopMass_sum ψ (n := m) (by omega)
  have hfin := f.sum_fin_eq_sum_range ψ
  rw [← hfin] at hsum
  rw [hsum]
  rw [stoppedMass, hcomplete, applyGate_one, f.stageState_mass ψ (n := m) (by omega)]
  exact measureProb_univ hnorm

/-- The final success mass of the frame is nonnegative. -/
theorem runSuccess_nonneg (f : CoherentVtFrame H m) (ψ : QState H) :
    0 ≤ f.runSuccess ψ := measureProb_nonneg _ _

/-- The final success mass is bounded by the total measurement mass of the input state. -/
theorem runSuccess_le_stateMass (f : CoherentVtFrame H m) (ψ : QState H) :
    f.runSuccess ψ ≤ MeasureProb ψ Finset.univ := by
  have h := projective_complement f.targetOrth (f.stageState ψ m (by omega))
  have hnonneg : 0 ≤ MeasureProb (ApplyGate (1 - f.target)
      (f.stageState ψ m (by omega))) Finset.univ := measureProb_nonneg _ _
  unfold runSuccess
  rw [← f.stageState_mass ψ (n := m) (by omega)]
  linarith

/-- Final running mass equals the input state's total mass minus the sum of fresh stopping
masses. -/
theorem runningMass_eq_one_sub_sum (f : CoherentVtFrame H m) (ψ : QState H) :
    MeasureProb (ApplyGate (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
        (f.stageState ψ m (by omega))) Finset.univ
      = MeasureProb ψ Finset.univ - (∑ j : Fin m, f.freshStopMass ψ j) := by
  have hsum := f.freshStopMass_sum ψ (n := m) (by omega)
  have hfin := f.sum_fin_eq_sum_range ψ
  rw [← hfin] at hsum
  have hstopdef : MeasureProb (ApplyGate (f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      (f.stageState ψ m (by omega))) Finset.univ = f.stoppedMass ψ m (by omega) := rfl
  have hcompl := projective_complement (f.stopNested.1 ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
    (f.stageState ψ m (by omega))
  have hnonneg : 0 ≤ MeasureProb (ApplyGate (1 - f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩)
      (f.stageState ψ m (by omega))) Finset.univ := measureProb_nonneg _ _
  rw [hstopdef, ← hsum] at hcompl
  rw [← f.stageState_mass ψ (n := m) (by omega)]
  linarith

/-- Fresh stopping projectors at distinct stages are orthogonal when the earlier projector is
multiplied by the later one. -/
theorem freshStop_disjoint (f : CoherentVtFrame H m) (j k : Fin m) (hjk : k.val < j.val) :
    f.freshStop k * f.freshStop j = 0 := by
  have hleK : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  have hleK1 : (⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  have hleK1' : (⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  have hleK2 : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  have h1 : f.stop ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
        * f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      = f.stop ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ :=
    f.stopNested.2 (⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)
      (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hleK1'
  have h2 : (f.stop ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) * f.stopAt j
      = f.stop ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ :=
    f.stopNested.2 (⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)
      (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hleK1
  have h3 : f.stopAt k * f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ = f.stopAt k :=
    f.stopNested.2 (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
      (⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hleK2
  have h4 : f.stopAt k * f.stopAt j = f.stopAt k :=
    f.stopNested.2 (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
      (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hleK
  simp only [freshStop]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
  rw [h1, h2, h3, h4]
  simp

/-- The input state in a stage record is the prefix state immediately before that stage. -/
theorem stageRecord_input (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    (f.stageRecord ψ j).inputState = f.stageState ψ j.val (by omega) := rfl

/-- The output state in a stage record is the prefix state immediately after that stage. -/
theorem stageRecord_output (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    (f.stageRecord ψ j).outputState = f.stageState ψ (j.val + 1) (by omega) := rfl

/-- The index stored in a stage record is the natural value of its finite stage index. -/
theorem stageRecord_stageIndex (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    (f.stageRecord ψ j).stageIndex = j.val := rfl

/-- The reached stopped projector in a stage record is the stopped-history projector immediately
after that stage. -/
theorem stageRecord_reachedStop (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    (f.stageRecord ψ j).reachedStop = f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := rfl

/-- The fresh stopped projector in a stage record is the frame's fresh stopping projector at
that stage. -/
theorem stageRecord_freshStop (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    (f.stageRecord ψ j).freshStop = f.freshStop j := rfl

/-- Applying a stage operator to its recorded input state yields its recorded output state. -/
theorem stageRecord_transition (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    ApplyGate (f.stageOp j) (f.stageRecord ψ j).inputState
      = (f.stageRecord ψ j).outputState := by
  rw [stageRecord_input, stageRecord_output, stageState_succ]

/-- A stage record's reached stopped projector splits into the previous stopped projector and
its recorded fresh stopping projector. -/
theorem stageRecord_reachedStop_split (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    (f.stageRecord ψ j).reachedStop = f.stopAt j + (f.stageRecord ψ j).freshStop := by
  rw [stageRecord_reachedStop, stageRecord_freshStop]
  exact f.stopHistory_split j

/-- Every stage at or after index `j` preserves the stopped projector at the beginning of stage
`j` under left projection. -/
theorem stop_mul_stageOp_later (f : CoherentVtFrame H m) (j k : Fin m) (hjk : j.val ≤ k.val) :
    f.stopAt j * f.stageOp k = f.stopAt j := by
  have hle : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1))
      ≤ ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  have hnest : f.stopAt j * f.stopAt k = f.stopAt j := f.stopNested.2 _ _ hle
  have hzero : f.stopAt j * (1 - f.stopAt k) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hnest]
    simp
  simp only [CoherentVtFrame.stageOp, coherentStage]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hzero, Matrix.zero_mul, hnest, _root_.add_zero]

/-- The total matrix of a list headed by `A` equals the tail's total matrix multiplied by `A`. -/
theorem listTotalOp_cons (A : Matrix H H ℂ) (C : List (Matrix H H ℂ)) :
    listTotalOp (A :: C) = listTotalOp C * A := by
  simp only [listTotalOp, List.foldr_cons]

/-- Appending a final gate multiplies the previous total matrix on the left by that gate. -/
theorem listTotalOp_append_singleton {C : List (Matrix H H ℂ)} (U : Matrix H H ℂ) :
    listTotalOp (C ++ [U]) = U * listTotalOp C := by
  induction C with
  | nil => simp [listTotalOp]
  | cons A C ih =>
    rw [List.cons_append]
    simp only [listTotalOp_cons]
    rw [ih, Matrix.mul_assoc]

/-- Running a list of matrix gates equals applying its total matrix to the input state. -/
theorem run_gates_eq_listTotalOp {C : List (Matrix H H ℂ)} (ψ : QState H) :
    Run 1 (C.map Step.gate) ψ = ApplyGate (listTotalOp C) ψ := by
  induction C generalizing ψ with
  | nil => simp [listTotalOp, applyGate_one]
  | cons U C ih =>
    rw [List.map_cons, Run, ih, ← applyGate_mul, listTotalOp_cons]

/-- The ordered list of the first `n` stage operators of a frame, for `n ≤ m`. -/
def stageOpsUpTo (f : CoherentVtFrame H m) (n : ℕ) (h : n ≤ m) : List (Matrix H H ℂ) :=
  match n with
  | 0 => []
  | n + 1 => stageOpsUpTo f n (Nat.le_of_succ_le h)
      ++ [f.stageOpAt n (Nat.lt_of_succ_le h)]

/-- The first `n` stage operators equal the list obtained by mapping stage operators over
`List.finRange n` with the index inclusion. -/
theorem stageOpsUpTo_eq_finRange (f : CoherentVtFrame H m) :
    ∀ (n : ℕ) (h : n ≤ m),
      (List.finRange n).map (fun i => f.stageOp (Fin.castLE h i)) = stageOpsUpTo f n h := by
  intro n
  induction n with
  | zero =>
    intro h
    rfl
  | succ n ih =>
    intro h
    have hn : n ≤ m := by omega
    have hcast : ∀ i : Fin n,
        f.stageOp (Fin.castLE h (Fin.castSucc i)) = f.stageOp (Fin.castLE hn i) := by
      intro i
      apply congrArg f.stageOp
      apply Fin.ext
      rfl
    have hmap : (List.map Fin.castSucc (List.finRange n)).map
        (fun i => f.stageOp (Fin.castLE h i))
        = (List.finRange n).map (fun i => f.stageOp (Fin.castLE hn i)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hcast i
    have hlast : f.stageOp (Fin.castLE h (Fin.last n)) = f.stageOpAt n (Nat.lt_of_succ_le h) := by
      apply congrArg f.stageOp
      apply Fin.ext
      rfl
    rw [List.finRange_succ_last, List.map_append, hmap]
    simp only [List.map_cons, List.map_nil]
    rw [hlast, ih]
    rfl

/-- The total matrix of the first `n` stage operators implements the frame's `n`-step evolution
starting at stage zero. -/
theorem stageOpsUpTo_apply (f : CoherentVtFrame H m) :
    ∀ (n : ℕ) (h : n ≤ m) (ψ : QState H),
      ApplyGate (listTotalOp (stageOpsUpTo f n h)) ψ
        = f.stageStateFrom ψ 0 n (by omega) := by
  intro n
  induction n with
  | zero =>
    intro h ψ
    simp [stageOpsUpTo, listTotalOp, CoherentVtFrame.stageStateFrom, applyGate_one]
  | succ n ih =>
    intro h ψ
    have hn : n ≤ m := by omega
    have hdecomp : stageOpsUpTo f (n + 1) h
        = stageOpsUpTo f n hn ++ [f.stageOpAt n (Nat.lt_of_succ_le h)] := rfl
    rw [hdecomp, listTotalOp_append_singleton, applyGate_mul, ih]
    have hstage : f.stageOpAt n (Nat.lt_of_succ_le h) = f.stageOp ⟨n, Nat.lt_of_succ_le h⟩ := rfl
    rw [hstage]
    rfl

/-- Applying the frame's total matrix produces its final stage-prefix state. -/
theorem totalOp_apply_eq_stageState (f : CoherentVtFrame H m) (ψ : QState H) :
    ApplyGate (f.totalOp) ψ = f.stageState ψ m (by omega) := by
  have hfin : stageOpsUpTo f m (le_refl m)
      = (List.finRange m).map (fun i => f.stageOp (Fin.castLE (le_refl m) i)) :=
    (stageOpsUpTo_eq_finRange f m (le_refl m)).symm
  have hcast : ∀ i : Fin m, f.stageOp (Fin.castLE (le_refl m) i) = f.stageOp i := by
    intro i
    apply congrArg f.stageOp
    apply Fin.ext
    rfl
  have htotal : f.totalOp = listTotalOp (stageOpsUpTo f m (le_refl m)) := by
    unfold totalOp
    rw [hfin]
    apply congrArg listTotalOp
    apply List.map_congr_left
    intro i _
    exact (hcast i).symm
  rw [htotal]
  have htraj := stageOpsUpTo_apply f m (le_refl m) ψ
  simpa only [CoherentVtFrame.stageState] using! htraj

/-- Running the coherent program produces the frame's final stage-prefix state. -/
theorem coherentProgram_run_eq (f : CoherentVtFrame H m) (ψ : QState H) :
    Run 1 (f.coherentProgram) ψ = f.stageState ψ m (by omega) := by
  have hfin : stageOpsUpTo f m (le_refl m)
      = (List.finRange m).map (fun i => f.stageOp (Fin.castLE (le_refl m) i)) :=
    (stageOpsUpTo_eq_finRange f m (le_refl m)).symm
  have hcast : ∀ i : Fin m, f.stageOp (Fin.castLE (le_refl m) i) = f.stageOp i := by
    intro i
    apply congrArg f.stageOp
    apply Fin.ext
    rfl
  have hprog : f.coherentProgram = (stageOpsUpTo f m (le_refl m)).map Step.gate := by
    unfold coherentProgram
    rw [hfin, List.map_map]
    apply List.map_congr_left
    intro i _
    exact congrArg Step.gate (hcast i).symm
  rw [hprog, run_gates_eq_listTotalOp]
  have htraj := stageOpsUpTo_apply f m (le_refl m) ψ
  simpa only [CoherentVtFrame.stageState] using! htraj

/-- The frozen and running fragments of a post-stage state sum to that state. -/
theorem stageState_frozen_running (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    f.frozenFragment (f.stageState ψ (j.val + 1) (by omega)) j
      + f.runningFragment (f.stageState ψ (j.val + 1) (by omega)) j
      = f.stageState ψ (j.val + 1) (by omega) := by
  simp only [CoherentVtFrame.frozenFragment, CoherentVtFrame.runningFragment]
  have hmul : ApplyGate (f.stopAt j) (f.stageState ψ (j.val + 1) (by omega))
      + ApplyGate (1 - f.stopAt j) (f.stageState ψ (j.val + 1) (by omega))
      = ApplyGate (f.stopAt j + (1 - f.stopAt j)) (f.stageState ψ (j.val + 1) (by omega)) := by
    simp only [ApplyGate, ← Matrix.add_mulVec]
  rw [hmul]
  have hsplit : f.stopAt j + (1 - f.stopAt j) = 1 := by abel
  rw [hsplit, applyGate_one]

/-- The running fragment has zero stopped projection, and the frozen fragment has zero
projection onto the complementary subspace. -/
theorem frozen_running_orthogonal (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    ApplyGate (f.stopAt j) (f.runningFragment ψ j) = 0 ∧
    ApplyGate (1 - f.stopAt j) (f.frozenFragment ψ j) = 0 := by
  have hid : f.stopAt j * f.stopAt j = f.stopAt j :=
    (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).1
  have hz1 : f.stopAt j * (1 - f.stopAt j) = 0 := by
    calc f.stopAt j * (1 - f.stopAt j) = f.stopAt j * 1 - f.stopAt j * f.stopAt j :=
        Matrix.mul_sub _ _ _
      _ = f.stopAt j - f.stopAt j * f.stopAt j := by rw [Matrix.mul_one]
      _ = f.stopAt j - f.stopAt j := by rw [hid]
      _ = 0 := sub_self _
  have hz2 : (1 - f.stopAt j) * f.stopAt j = 0 := by
    calc (1 - f.stopAt j) * f.stopAt j = 1 * f.stopAt j - f.stopAt j * f.stopAt j :=
        Matrix.sub_mul _ _ _
      _ = f.stopAt j - f.stopAt j * f.stopAt j := by rw [Matrix.one_mul]
      _ = f.stopAt j - f.stopAt j := by rw [hid]
      _ = 0 := sub_self _
  constructor
  · simp only [CoherentVtFrame.runningFragment]
    rw [← applyGate_mul, hz1]
    simp only [ApplyGate, Matrix.zero_mulVec]
  · simp only [CoherentVtFrame.frozenFragment]
    rw [← applyGate_mul, hz2]
    simp only [ApplyGate, Matrix.zero_mulVec]

/-- The component stopped before stage `j` is unchanged at every later valid prefix. -/
theorem frozenFragment_frozen (f : CoherentVtFrame H m) (ψ : QState H) (j k : Fin m)
    (hjk : j.val ≤ k.val) :
    f.frozenFragment (f.stageState ψ k.val (by omega)) j
      = f.frozenFragment (f.stageState ψ j.val (by omega)) j := by
  have hmain : ∀ (n : ℕ) (hmn : j.val ≤ n) (hn : n ≤ m),
      ApplyGate (f.stopAt j) (f.stageState ψ n hn)
        = ApplyGate (f.stopAt j) (f.stageState ψ j.val (Nat.le_of_lt j.isLt)) := by
    intro n hmn hn
    refine Nat.le_induction (m := j.val)
      (P := fun k _ => ∀ (hb : k ≤ m),
        ApplyGate (f.stopAt j) (f.stageState ψ k hb)
          = ApplyGate (f.stopAt j) (f.stageState ψ j.val (Nat.le_of_lt j.isLt)))
      (fun hnb => ?_) (fun k hk ih => ?_) n hmn hn
    · rfl
    · intro hkb
      have hstep : f.stageState ψ (k + 1) (by omega)
          = ApplyGate (f.stageOp ⟨k, by omega⟩) (f.stageState ψ k (by omega)) := by
        rfl
      rw [hstep, ← applyGate_mul]
      have hfin : f.stageOp ⟨k, by omega⟩ = f.stageOp ⟨k, Nat.lt_of_succ_le hkb⟩ := rfl
      rw [hfin]
      have hstop : f.stopAt j * f.stageOp ⟨k, Nat.lt_of_succ_le hkb⟩ = f.stopAt j :=
        f.stop_mul_stageOp_later j ⟨k, Nat.lt_of_succ_le hkb⟩ hk
      rw [hstop]
      exact ih (Nat.le_of_succ_le hkb)
  have hk : k.val ≤ m := by omega
  have h := hmain k.val hjk hk
  simpa only [CoherentVtFrame.frozenFragment] using! h

/-- The post-stage running fragment agrees with the corresponding fragment obtained by applying
the underlying round to the preceding prefix state. -/
theorem runningFragment_transported (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    f.runningFragmentAfter (f.stageState ψ (j.val + 1) (by omega)) j
      = f.runningFragmentAfter
          (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))) j := by
  have hstep : f.stageState ψ (j.val + 1) (by omega)
      = ApplyGate (f.stageOp j) (f.stageState ψ j.val (by omega)) :=
    f.stageState_succ ψ j.val (by omega)
  have hround : (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stageOp j
      = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.round j :=
    f.runningPart_step j
  simp only [CoherentVtFrame.runningFragmentAfter]
  rw [hstep, ← applyGate_mul, hround, ← applyGate_mul]

/-- The three-gate circuit consisting of a target marking, the stage's base operator, and
another target marking. -/
def stageWord (f : CoherentVtFrame H m) (j : Fin m) : Circuit H :=
  [Step.gate (targetMark f.target), Step.gate (f.base j), Step.gate (targetMark f.target)]

/-- The three-gate circuit with target markings around the conjugate transpose of the stage's
base operator. -/
def stageWordInverse (f : CoherentVtFrame H m) (j : Fin m) : Circuit H :=
  [Step.gate (targetMark f.target), Step.gate (f.base j)ᴴ, Step.gate (targetMark f.target)]

/-- The total matrix of the target-marked base-operator stage circuit. -/
def stageWordMatrix (f : CoherentVtFrame H m) (j : Fin m) : Matrix H H ℂ :=
  listTotalOp [targetMark f.target, f.base j, targetMark f.target]

/-- The total matrix of the target-marked conjugate-transpose base-operator circuit. -/
def stageWordInverseMatrix (f : CoherentVtFrame H m) (j : Fin m) : Matrix H H ℂ :=
  listTotalOp [targetMark f.target, (f.base j)ᴴ, targetMark f.target]

/-- The total matrix of the stage circuit equals the frame's round matrix. -/
theorem stageWordMatrix_eq (f : CoherentVtFrame H m) (j : Fin m) :
    f.stageWordMatrix j = f.round j := by
  simp only [stageWordMatrix, listTotalOp, List.foldr_cons, List.foldr_nil, Matrix.one_mul]
  simp only [round, stageRound, targetMark]

/-- The total matrix of the inverse stage circuit equals the conjugate transpose of the round
matrix. -/
theorem stageWordInverseMatrix_eq (f : CoherentVtFrame H m) (j : Fin m) :
    f.stageWordInverseMatrix j = (f.round j)ᴴ := by
  have hR : (ReflectionAbout f.target)ᴴ = ReflectionAbout f.target :=
    reflectionAbout_conjTranspose f.targetOrth
  have hR' : (targetMark f.target)ᴴ = targetMark f.target := by
    simp only [targetMark]
    exact reflectionAbout_conjTranspose f.targetOrth
  have hL : listTotalOp [targetMark f.target, (f.base j)ᴴ, targetMark f.target]
      = (ReflectionAbout f.target * (f.base j)ᴴ) * ReflectionAbout f.target := by
    simp only [listTotalOp, List.foldr_cons, List.foldr_nil, Matrix.one_mul, targetMark]
  have hR2 : (f.round j)ᴴ = ReflectionAbout f.target
      * ((f.base j)ᴴ * ReflectionAbout f.target) := by
    rw [round, stageRound]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR]
  simp only [stageWordInverseMatrix]
  rw [hL, hR2, Matrix.mul_assoc]

end CoherentVtFrame

/-- The stage-visit count for `k` amplification rounds, given by `stageVisits k`. -/
def stageVisitCount (k : ℕ) : ℕ := stageVisits k

/-- The flag-reflection count for `k` amplification rounds, given by `stageFlagCount k`. -/
def stageFlagReflections (k : ℕ) : ℕ := stageFlagCount k

/-- The query count for `k` amplification rounds, equal to the stage-visit count. -/
def stageQueryCount (k : ℕ) : ℕ := stageVisits k

/-- The inverse-program query count for `k` amplification rounds, equal to the stage-visit
count. -/
def stageInverseQueryCount (k : ℕ) : ℕ := stageVisits k

/-- Stage access time equals the visit count times the duration of one visit. -/
theorem stageTime_eq (j k : ℕ) :
    stageTime j k = stageVisitCount k * stageVisitTime j := rfl

/-- The access time of stage `j` with `k` amplification rounds is `(2 * k + 1) * 2^j`. -/
theorem stageTime_eq_visits_dyadic (j k : ℕ) :
    stageTime j k = (2 * k + 1) * 2 ^ j := by
  simp only [stageTime, stageVisitTime, stageVisits]

/-- The inverse stage program has the same access time as the forward stage program. -/
theorem stageInverseTime_eq (j k : ℕ) :
    stageInverseTime j k = stageTime j k := rfl

/-- The stage charge is the visit count times the visit duration plus the flag-reflection count
times the flag price. -/
theorem stageCharge_eq (j k : ℕ) (flagPrice : ℕ) :
    stageTime j k + stageFlagReflections k * flagPrice
      = stageVisitCount k * stageVisitTime j + stageFlagReflections k * flagPrice := rfl

/-- The flag-reflection count is twice the stage-visit count. -/
theorem stageFlagReflections_eq (k : ℕ) :
    stageFlagReflections k = 2 * stageVisitCount k := by
  simp only [stageFlagReflections, stageFlagCount, stageVisitCount, stageVisits, roundFlagCount]
  omega

/-- The inverse stage program has the same query count as the forward stage program. -/
theorem stageInverseQueryCount_eq (k : ℕ) :
    stageInverseQueryCount k = stageQueryCount k := rfl

/-- The sum of stopping weights times squared dyadic stopping times over the finite stage set. -/
def stopSecondMoment (m : ℕ) (q : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, q j * (stopTime j.val) ^ 2

/-- The square root of the stopping-time second moment. -/
def averageStopTime (m : ℕ) (q : Fin m → ℝ) : ℝ :=
  Real.sqrt (stopSecondMoment m q)

/-- For nonnegative stopping weights, the second moment equals the square of the average
stopping-time quantity. -/
theorem stopSecondMoment_eq_averageSq {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) :
    stopSecondMoment m q = (averageStopTime m q) ^ 2 := by
  have hnonneg : 0 ≤ stopSecondMoment m q := by
    refine Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (hq j) (sq_nonneg _)
  rw [averageStopTime, Real.sq_sqrt hnonneg]

/-- The maximum dyadic stopping-time parameter `2^m`. -/
def maxStopTime (m : ℕ) : ℝ := (2 : ℝ) ^ m

/-- The dyadic stopping time of every stage in `Fin m` is at most `maxStopTime m`. -/
theorem stopTime_le_max (m : ℕ) (j : Fin m) :
    (stopTime j.val) ≤ maxStopTime m := by
  have hle : j.val + 1 ≤ m := by omega
  have hn : (2 : ℕ) ^ (j.val + 1) ≤ (2 : ℕ) ^ m :=
    pow_le_pow_right' (a := (2 : ℕ)) (by norm_num) hle
  have hpow : (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ m := by exact_mod_cast hn
  unfold stopTime maxStopTime
  exact hpow

/-- For nonnegative stopping weights with total mass at most one, the second moment is at most
the maximum time times the average stopping time. -/
theorem stopSecondMoment_le_max_mul_average {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : (∑ j : Fin m, q j) ≤ 1) :
    stopSecondMoment m q ≤ maxStopTime m * averageStopTime m q := by
  have hqsum_nonneg : 0 ≤ ∑ j : Fin m, q j := Finset.sum_nonneg fun j _ => hq j
  have hsecond : (∑ j : Fin m, q j * stopTime j.val) ≤ averageStopTime m q := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m))
      (fun j => Real.sqrt (q j)) (fun j => Real.sqrt (q j) * stopTime j.val)
    have hleft : (∑ j : Fin m, Real.sqrt (q j) * (Real.sqrt (q j) * stopTime j.val))
        = ∑ j : Fin m, q j * stopTime j.val := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsq : Real.sqrt (q j) ^ 2 = q j := Real.sq_sqrt (hq j)
      rw [← mul_assoc, ← sq, hsq]
    have hmid : (∑ j : Fin m, (Real.sqrt (q j)) ^ 2) = ∑ j : Fin m, q j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact Real.sq_sqrt (hq j)
    have hright : (∑ j : Fin m, (Real.sqrt (q j) * stopTime j.val) ^ 2)
        = ∑ j : Fin m, q j * (stopTime j.val) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (hq j)]
    rw [hleft, hmid, hright] at hcs
    have hsqrt1 : Real.sqrt (∑ j : Fin m, q j) ≤ 1 := by
      have hsq : (Real.sqrt (∑ j : Fin m, q j)) ^ 2 = ∑ j : Fin m, q j :=
        Real.sq_sqrt hqsum_nonneg
      by_cases hz : Real.sqrt (∑ j : Fin m, q j) = 0
      · simp [hz]
      · have hpos : 0 < Real.sqrt (∑ j : Fin m, q j) :=
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
        by_contra hcon
        have hlt : 1 < Real.sqrt (∑ j : Fin m, q j) := lt_of_not_ge hcon
        have hmul := mul_lt_mul_of_pos_right hlt hpos
        rw [one_mul, ← sq, hsq] at hmul
        linarith
    calc
      (∑ j : Fin m, q j * stopTime j.val)
          ≤ Real.sqrt (∑ j : Fin m, q j) * Real.sqrt (stopSecondMoment m q) := hcs
      _ ≤ 1 * Real.sqrt (stopSecondMoment m q) := by
        exact mul_le_mul_of_nonneg_right hsqrt1 (Real.sqrt_nonneg _)
      _ = averageStopTime m q := by rw [averageStopTime]; ring
  have hterm : ∀ j : Fin m, q j * (stopTime j.val) ^ 2
      ≤ q j * (stopTime j.val * maxStopTime m) := by
    intro j
    have hstop : 0 ≤ stopTime j.val := by
      unfold stopTime
      positivity
    have hle : stopTime j.val ≤ maxStopTime m := stopTime_le_max m j
    have hsq : (stopTime j.val) ^ 2 ≤ stopTime j.val * maxStopTime m := by nlinarith
    have hmul : q j * (stopTime j.val) ^ 2 ≤ q j * (stopTime j.val * maxStopTime m) :=
      mul_le_mul_of_nonneg_left hsq (hq j)
    have hre : q j * (stopTime j.val * maxStopTime m) = q j * stopTime j.val * maxStopTime m := by
      ring
    exact hmul
  have hfirst : stopSecondMoment m q
      ≤ maxStopTime m * (∑ j : Fin m, q j * stopTime j.val) := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) fun j _ => hterm j
    have hre : (∑ j : Fin m, q j * (stopTime j.val * maxStopTime m))
        = maxStopTime m * (∑ j : Fin m, q j * stopTime j.val) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hre] at hsum
    exact hsum
  have hmax : 0 ≤ maxStopTime m := by
    unfold maxStopTime
    positivity
  calc
    stopSecondMoment m q ≤ maxStopTime m * (∑ j : Fin m, q j * stopTime j.val) := hfirst
    _ ≤ maxStopTime m * averageStopTime m q :=
      mul_le_mul_of_nonneg_left hsecond hmax

/-- The bound `maxStopTime m * Tav / p` for a success-rescaled stopping-time second moment. -/
def meanSquareBound (m : ℕ) (Tav p : ℝ) : ℝ :=
  maxStopTime m * Tav / p

/-- The stopping-time second moment divided by the success parameter `p`. -/
def amplifiedSecondMoment {m : ℕ} (q : Fin m → ℝ) (p : ℝ) : ℝ :=
  stopSecondMoment m q / p

/-- For a nonnegative stopping distribution of mass at most one and positive `p`, the rescaled
second moment is bounded by `meanSquareBound`. -/
theorem amplified_stopSecondMoment_le {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : (∑ j : Fin m, q j) ≤ 1) (p : ℝ) (hp : 0 < p) :
    amplifiedSecondMoment q p ≤ meanSquareBound m (averageStopTime m q) p := by
  have hbase := stopSecondMoment_le_max_mul_average q hq hsum
  have hTav : 0 ≤ averageStopTime m q := Real.sqrt_nonneg _
  have h1 : stopSecondMoment m q / p ≤ (maxStopTime m * averageStopTime m q) / p :=
    div_le_div_of_nonneg_right hbase (le_of_lt hp)
  have h2 : (maxStopTime m * averageStopTime m q) / p
      = maxStopTime m * (averageStopTime m q / p) := by ring
  calc
    stopSecondMoment m q / p ≤ (maxStopTime m * averageStopTime m q) / p := h1
    _ = maxStopTime m * (averageStopTime m q / p) := h2
    _ = meanSquareBound m (averageStopTime m q) p := by
      unfold meanSquareBound
      ring

/-- The adaptive second-moment bound `B * Tav / p` using a supplied maximum-time bound `B`. -/
def adaptiveMeanSquareBound (B : ℝ) (Tav p : ℝ) : ℝ :=
  B * Tav / p

/-- For nonnegative stopping weights of total mass at most one and positive `p`, a bound `B ≥
maxStopTime m` yields the adaptive rescaled second-moment bound. -/
theorem adaptive_stopSecondMoment_le {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hsum : (∑ j : Fin m, q j) ≤ 1) (p : ℝ) (hp : 0 < p)
    (c qhat : ℝ) (hacc : estimateAccurate c p qhat) (B : ℝ) (hB : maxStopTime m ≤ B) :
    stopSecondMoment m q / p ≤ adaptiveMeanSquareBound B (averageStopTime m q) p := by
  have hbase := stopSecondMoment_le_max_mul_average q hq hsum
  have h1 : stopSecondMoment m q / p ≤ (B * averageStopTime m q) / p := by
    have hBmax : maxStopTime m * averageStopTime m q ≤ B * averageStopTime m q :=
      mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg _)
    exact div_le_div_of_nonneg_right (hbase.trans hBmax) (le_of_lt hp)
  unfold adaptiveMeanSquareBound
  calc
    stopSecondMoment m q / p ≤ (B * averageStopTime m q) / p := h1
    _ = B * averageStopTime m q / p := by ring

/-- Replacing the maximum stopping time by a larger bound increases the second-moment bound when
`Tav ≥ 0` and `p > 0`. -/
theorem meanSquareBound_le_adaptiveBound (m : ℕ) (Tav p B : ℝ)
    (hB : maxStopTime m ≤ B) (hTav : 0 ≤ Tav) (hp : 0 < p) :
    meanSquareBound m Tav p ≤ adaptiveMeanSquareBound B Tav p := by
  have h1 : maxStopTime m * Tav ≤ B * Tav := mul_le_mul_of_nonneg_right hB hTav
  unfold meanSquareBound adaptiveMeanSquareBound
  exact div_le_div_of_nonneg_right h1 (le_of_lt hp)

/-- For `0 < p ≤ 1`, the iterated logarithmic factor is at least one. -/
theorem iteratedLogFactor_ge_one {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    1 ≤ iteratedLogFactor p := by
  have hmax : max p (1 / 2) ≤ 1 := by
    rw [max_def]
    split_ifs with h
    · exact (by norm_num : (1 / 2 : ℝ) ≤ 1)
    · exact hp1
  have hpos : 0 < max p (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hinv : 1 ≤ 1 / max p (1 / 2) := by
    rw [le_div_iff₀ hpos]
    simpa using! hmax
  have hlog1 : 0 ≤ Real.log (1 / max p (1 / 2)) := Real.log_nonneg hinv
  have hsum : 1 ≤ 1 + Real.log (1 / max p (1 / 2)) := by linarith
  have hlog2 : 0 ≤ Real.log (1 + Real.log (1 / max p (1 / 2))) := Real.log_nonneg hsum
  unfold iteratedLogFactor
  linarith

/-- The adaptive estimation budget is nonnegative for nonnegative budget parameters and a
success parameter in `(0, 1]`. -/
theorem adaptiveEstimateBudget_nonneg {k p q : ℝ} (hk : 0 ≤ k) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 ≤ q) : 0 ≤ adaptiveEstimateBudget k p q := by
  unfold adaptiveEstimateBudget
  have hmax : 0 < max q p := lt_of_lt_of_le hp (le_max_right q p)
  have hsqrt : 0 < Real.sqrt (max q p) := Real.sqrt_pos.2 hmax
  have hlog : 1 ≤ iteratedLogFactor p := iteratedLogFactor_ge_one hp hp1
  have h1 : 0 ≤ k * iteratedLogFactor p := mul_nonneg hk (by linarith)
  exact div_nonneg h1 (le_of_lt hsqrt)

/-- The sum of the adaptive second-moment bound and the adaptive estimation budget. -/
def adaptiveTotalBound (k B Tav p q : ℝ) : ℝ :=
  adaptiveMeanSquareBound B Tav p + adaptiveEstimateBudget k p q

/-- For nonnegative estimation parameters and `0 < p ≤ 1`, the adaptive total bound is at least
its second-moment component. -/
theorem adaptiveTotalBound_ge {k B Tav p q : ℝ} (hk : 0 ≤ k) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 ≤ q) :
    adaptiveMeanSquareBound B Tav p ≤ adaptiveTotalBound k B Tav p q := by
  unfold adaptiveTotalBound
  have h1 : 0 ≤ adaptiveEstimateBudget k p q :=
    adaptiveEstimateBudget_nonneg hk hp hp1 hq
  linarith

/-- Under the stopping-weight, success, estimate, and maximum-time assumptions, the rescaled
second moment satisfies both bounds and the nonadaptive, adaptive, and total bounds are
ordered. -/
theorem nonadaptive_le_adaptive {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hsum : (∑ j : Fin m, q j) ≤ 1) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (c qhat : ℝ) (hacc : estimateAccurate c p qhat) (B : ℝ) (hB : maxStopTime m ≤ B)
    (k qmeas : ℝ) (hk : 0 ≤ k) (hqmeas : 0 ≤ qmeas) :

    amplifiedSecondMoment q p ≤ meanSquareBound m (averageStopTime m q) p ∧

    stopSecondMoment m q / p ≤ adaptiveMeanSquareBound B (averageStopTime m q) p ∧

    meanSquareBound m (averageStopTime m q) p
      ≤ adaptiveMeanSquareBound B (averageStopTime m q) p ∧

    adaptiveMeanSquareBound B (averageStopTime m q) p
      ≤ adaptiveTotalBound k B (averageStopTime m q) p qmeas := by
  refine ⟨amplified_stopSecondMoment_le q hq hsum p hp,
    adaptive_stopSecondMoment_le q hq hsum p hp c qhat hacc B hB, ?_, ?_⟩
  · exact meanSquareBound_le_adaptiveBound m (averageStopTime m q) p B hB
      (Real.sqrt_nonneg _) hp
  · exact adaptiveTotalBound_ge hk hp hp1 hqmeas

/-- A complete coherent frame with positive stage count and normalized input yields
`stopTimeData` from its fresh stopping masses and dyadic stopping times. -/
theorem vtStopTimeData (f : CoherentVtFrame H m) (ψ : QState H) (hm : 0 < m)
    (hcomplete : f.stop ⟨m, Nat.lt_succ_of_le (le_refl m)⟩ = 1)
    (hnorm : Normalized ψ) :
    stopTimeData m (fun j => f.freshStopMass ψ j) (fun j => stopTime j.val)
      (maxStopTime m) (averageStopTime m (fun j => f.freshStopMass ψ j)) := by
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact f.freshStopMass_nonneg ψ j
  · exact f.freshStopMass_total_eq_one ψ hcomplete hnorm
  · intro j
    simp only [stopTime]
    positivity
  · intro j
    exact stopTime_le_max m j
  · have hm1 : (1 : ℕ) ≤ m := hm
    have h2 : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) hm1
    unfold maxStopTime
    linarith
  · have h := stopSecondMoment_eq_averageSq (fun j => f.freshStopMass ψ j)
      (fun j => f.freshStopMass_nonneg ψ j)
    rw [← h]
    rfl

/-- The square-root average stopping-time quantity is nonnegative for every weight function. -/
theorem averageStopTime_nonneg {m : ℕ} (q : Fin m → ℝ) :
    0 ≤ averageStopTime m q := Real.sqrt_nonneg _

/-- The source logarithmic factor at the maximum stopping time equals `1 + log (max 1
(maxStopTime m))`. -/
theorem sourceLogFactor (f : CoherentVtFrame H m) :
    tightLogFactor (maxStopTime m) = 1 + Real.log (max 1 (maxStopTime m)) := rfl

/-- Expands `tightAccessCost` into its maximum-time and average-time terms with the logarithmic
factors used in [Ambainis, Theorem 1][Ambainis2012]. -/
theorem sourceAccessConstant (f : CoherentVtFrame H m) (ψ : QState H) (p : ℝ)
    (hp : 0 < p) :
    tightAccessCost (maxStopTime m) (averageStopTime m (fun j => f.freshStopMass ψ j)) p
      = maxStopTime m * Real.sqrt (tightLogFactor (maxStopTime m))
        + averageStopTime m (fun j => f.freshStopMass ψ j)
          * (tightLogFactor (maxStopTime m)) ^ ((3 : ℝ) / 2)
          / Real.sqrt p := by
  rfl

/-- The cumulative time starting at zero and recursively multiplying the previous time plus a
dyadic stage duration by the scheduled odd amplification factor. -/
def sourceCumulativeTime (k : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => (2 * k (i + 1) + 1 : ℝ) * (sourceCumulativeTime k i + (2 : ℝ) ^ i)

/-- Every cumulative time generated by the source recurrence is nonnegative. -/
theorem sourceCumulativeTime_nonneg (k : ℕ → ℕ) : ∀ i, 0 ≤ sourceCumulativeTime k i := by
  intro i
  induction i with
  | zero => simp [sourceCumulativeTime]
  | succ i ih =>
      have h1 : 0 ≤ (2 : ℝ) ^ i := by positivity
      have h2 : 0 ≤ (2 * k (i + 1) + 1 : ℝ) := by positivity
      simp only [sourceCumulativeTime]
      exact mul_nonneg h2 (by linarith)

/-- At each positive index, cumulative time satisfies the odd-multiplier recurrence with the
previous time and the next dyadic stage duration. -/
theorem sourceCumulativeTime_rec (k : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    sourceCumulativeTime k i
      = (2 * k i + 1 : ℝ) * (sourceCumulativeTime k (i - 1) + (2 : ℝ) ^ (i - 1)) := by
  have h1 : i - 1 + 1 = i := by omega
  rw [← h1]
  rfl

/-- The odd-multiplier dyadic access charge at a valid natural stage index, extended by zero
outside the stage range. -/
def chargedAccessTimeAt (rounds : Fin m → ℕ) (j : ℕ) : ℝ :=
  if hj : j < m then (2 * rounds ⟨j, hj⟩ + 1 : ℝ) * (2 : ℝ) ^ j else 0

/-- The sum over stages of odd amplification multipliers times dyadic stage durations. -/
def chargedAccessTime (rounds : Fin m → ℕ) : ℝ :=
  ∑ j : Fin m, (2 * rounds j + 1 : ℝ) * (2 : ℝ) ^ j.val

/-- Total charged access time equals the range sum of the natural-index stage charges. -/
theorem chargedAccessTime_eq_sum_at (rounds : Fin m → ℕ) :
    chargedAccessTime rounds = ∑ j ∈ Finset.range m, chargedAccessTimeAt rounds j := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hlt : j.val < m := j.isLt
  rw [chargedAccessTimeAt, dif_pos hlt]

/-- When the finite schedule agrees with the source recurrence schedule, charged access time is
bounded by the final source cumulative time. -/
theorem chargedAccessTime_le_sourceTime (k : ℕ → ℕ) (rounds : Fin m → ℕ)
    (hk : ∀ j : Fin m, k (j.val + 1) = rounds j) :
    chargedAccessTime rounds ≤ sourceCumulativeTime k m := by
  have hsum : chargedAccessTime rounds = ∑ j ∈ Finset.range m, chargedAccessTimeAt rounds j :=
    chargedAccessTime_eq_sum_at rounds
  have hprefix : ∀ n : ℕ, n ≤ m →
      (∑ j ∈ Finset.range n, chargedAccessTimeAt rounds j) ≤ sourceCumulativeTime k n := by
    intro n hn
    induction n with
    | zero => simp [sourceCumulativeTime]
    | succ n ih =>
        have hn' : n + 1 ≤ m := hn
        have hle : n ≤ m := Nat.le_of_succ_le hn
        have hlt : n < m := Nat.lt_of_succ_le hn'
        have hsum' : (∑ j ∈ Finset.range n, chargedAccessTimeAt rounds j)
            ≤ sourceCumulativeTime k n := ih hle
        have hc : chargedAccessTimeAt rounds n
            = (2 * rounds ⟨n, hlt⟩ + 1 : ℝ) * (2 : ℝ) ^ n := by
          simp [chargedAccessTimeAt, hlt]
        have hk' : k (n + 1) = rounds ⟨n, hlt⟩ := hk ⟨n, hlt⟩
        rw [Finset.sum_range_succ, hc, sourceCumulativeTime, hk']
        have hT : 0 ≤ sourceCumulativeTime k n := sourceCumulativeTime_nonneg k n
        have ha : (1 : ℝ) ≤ 2 * rounds ⟨n, hlt⟩ + 1 := by
          have h0 : (0 : ℝ) ≤ 2 * rounds ⟨n, hlt⟩ + 1 := by positivity
          linarith
        nlinarith
  rw [hsum]
  exact hprefix m (le_refl m)

/-- Positive base weights, amplified-weight floors, and gain windows bound charged access time
by the corrected gain-product expression from equation (6) of [Ambainis2012]. -/
theorem chargedAccessTime_le_sourceEq6 (rounds : Fin m → ℕ)
    (k : ℕ → ℕ) (rs rs' : ℕ → ℝ)
    (hk : ∀ j : Fin m, k (j.val + 1) = rounds j)
    (hm : 1 ≤ m)
    (hpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < rs' j)
    (hfloor : ∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j)
    (hwin : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * rs' j ≤ rs j) :
    chargedAccessTime rounds
      ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct rs rs' 1 (m + 1) * sourceCumulativeTime k 0
          + eq6ProductSum rs rs' m) := by
  have hsrc := clause89_event_bounds m rs rs' k (sourceCumulativeTime k) hm hpos hfloor hwin
    (sourceCumulativeTime_nonneg k 0) (fun i hi1 hi2 => sourceCumulativeTime_rec k hi1)
  exact (chargedAccessTime_le_sourceTime k rounds hk).trans hsrc.2

/-- Summing a natural-valued function over `List.finRange m` equals its finite sum over `Fin m`. -/
theorem sum_finRange_map_nat (m : ℕ) (f : Fin m → ℕ) :
    ((List.finRange m).map f).sum = ∑ j : Fin m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
      have h2 := ih (f ∘ Fin.succ)
      rw [h2, Fin.sum_univ_succ]
      rfl

namespace CoherentVtFrame

variable {m : ℕ}

/-- The adjoint of a concatenated word is the adjoint of the second word followed by the adjoint
of the first. -/
private theorem wordAdjoint_append {H : Type} {r : ℕ} (C D : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (C ++ D) = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint D ++ Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint C := by
  unfold Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint
  simp [List.reverse_append, List.map_append]

/-- Weighted oracle cost is additive under word concatenation. -/
private theorem weightedCost_append {H : Type} {r : ℕ} (prices : ℕ → ℕ)
    (C D : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices (C ++ D)
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices C + Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices D := by
  simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, List.map_append, List.sum_append]

/-- The known-gate count is additive under word concatenation. -/
private theorem gateCount_append {H : Type} {r : ℕ} (C D : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (C ++ D) = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount C + Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount D := by
  simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount, List.countP_append]

/-- The weighted cost of a flattened list of words equals the sum of their weighted costs. -/
private theorem weightedCost_flatten {H : Type} {r : ℕ} (prices : ℕ → ℕ) :
    ∀ (C : List (Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H r)),
      Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices C.flatten
        = (C.map (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices)).sum := by
  intro C
  induction C with
  | nil => simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost]
  | cons w C ih =>
    show Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost prices (w :: C).flatten = _
    simp only [List.flatten_cons, weightedCost_append, ih, List.map_cons, List.sum_cons]

/-- The paid stage word with multiplicity `n` makes exactly `n` calls to its stage's oracle
slot. -/
theorem stagePaidWord_calls (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j n) j.val = n := by
  induction n with
  | zero => simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.calls, CoherentVtFrame.stagePaidWord]
  | succ n ih =>
    have hpre : f.stagePaidWord j (n + 1)
        = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    have happ : Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidRound j ++ f.stagePaidWord j n) j.val
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidRound j) j.val
          + Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j n) j.val :=
      calls_append (f.stagePaidRound j) (f.stagePaidWord j n) j.val
    have hround : Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidRound j) j.val = 1 := by
      simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.calls, CoherentVtFrame.stagePaidRound]
    rw [hpre, happ, hround, ih]
    ring

/-- The paid stage word for `k` amplification rounds makes exactly `2 * k + 1` calls to its
oracle slot. -/
theorem stagePaidWord_calls_amp (f : CoherentVtFrame H m) (j : Fin m) (k : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j (2 * k + 1)) j.val = 2 * k + 1 :=
  f.stagePaidWord_calls j (2 * k + 1)

/-- A paid stage word of multiplicity `n` contains exactly `2 * n` known gates. -/
theorem stagePaidWord_gateCount (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j n) = 2 * n := by
  induction n with
  | zero => simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount, CoherentVtFrame.stagePaidWord]
  | succ n ih =>
    have hpre : f.stagePaidWord j (n + 1)
        = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    have happ : Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidRound j ++ f.stagePaidWord j n)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidRound j) + Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j n) :=
      gateCount_append (f.stagePaidRound j) (f.stagePaidWord j n)
    have hround : Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidRound j) = 2 := by
      simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount, CoherentVtFrame.stagePaidRound]
    rw [hpre, happ, hround, ih]
    ring

/-- The weighted access time of a paid stage word of multiplicity `n` is `n` times its dyadic
stage duration. -/
theorem stagePaidWord_accessTime (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j n)
      = n * stageDuration j.val := by
  induction n with
  | zero => simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, CoherentVtFrame.stagePaidWord]
  | succ n ih =>
    have hpre : f.stagePaidWord j (n + 1)
        = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    have happ : Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration
          (f.stagePaidRound j ++ f.stagePaidWord j n)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidRound j)
          + Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j n) :=
      weightedCost_append stageDuration (f.stagePaidRound j) (f.stagePaidWord j n)
    have hround : Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidRound j)
        = stageDuration j.val := by
      simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, CoherentVtFrame.stagePaidRound]
    rw [hpre, happ, hround, ih]
    ring

/-- The paid stage word for `k` amplification rounds has access time `(2 * k + 1) *
stageDuration j.val`. -/
theorem stagePaidWord_accessTime_amp (f : CoherentVtFrame H m) (j : Fin m) (k : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * k + 1))
      = (2 * k + 1) * stageDuration j.val :=
  f.stagePaidWord_accessTime j (2 * k + 1)

/-- The inverse paid stage round is the word adjoint of the forward paid stage round. -/
theorem stagePaidRoundInverse_eq_wordAdjoint (f : CoherentVtFrame H m) (j : Fin m) :
    f.stagePaidRoundInverse j = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (f.stagePaidRound j) := by
  unfold Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint
  simp [CoherentVtFrame.stagePaidRoundInverse, CoherentVtFrame.stagePaidRound,
    f.flagReflection_conjTranspose]

/-- The inverse paid stage word is the word adjoint of the forward paid stage word. -/
theorem stagePaidWordInverse_eq_wordAdjoint (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    f.stagePaidWordInverse j n = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (f.stagePaidWord j n) := by
  induction n with
  | zero => simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint, CoherentVtFrame.stagePaidWord,
      CoherentVtFrame.stagePaidWordInverse]
  | succ n ih =>
    have hpre : f.stagePaidWord j (n + 1)
        = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    have hpre' : f.stagePaidWordInverse j (n + 1)
        = f.stagePaidWordInverse j n ++ f.stagePaidRoundInverse j := rfl
    have happ : Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (f.stagePaidRound j ++ f.stagePaidWord j n)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (f.stagePaidWord j n) ++ Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (f.stagePaidRound j) :=
      wordAdjoint_append (f.stagePaidRound j) (f.stagePaidWord j n)
    rw [hpre, hpre', happ, ih, f.stagePaidRoundInverse_eq_wordAdjoint j]

/-- For any oracle matrices, the inverse paid stage word has matrix equal to the conjugate
transpose of the forward word matrix. -/
theorem stagePaidWord_matrix_adjoint (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ)
    (oracles : ℕ → Matrix H H ℂ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (f.stagePaidWordInverse j n)
      = (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles (f.stagePaidWord j n))ᴴ := by
  rw [f.stagePaidWordInverse_eq_wordAdjoint j n]
  exact wordMatrix_wordAdjoint oracles (f.stagePaidWord j n)

/-- Inverting a paid stage word preserves the number of calls to its stage's oracle slot. -/
theorem stagePaidWordInverse_calls (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWordInverse j n) j.val
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j n) j.val := by
  rw [f.stagePaidWordInverse_eq_wordAdjoint j n, calls_wordAdjoint]

/-- Inverting a paid stage word preserves its weighted dyadic access time. -/
theorem stagePaidWordInverse_accessTime (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWordInverse j n)
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j n) := by
  induction n with
  | zero => simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, CoherentVtFrame.stagePaidWord,
    CoherentVtFrame.stagePaidWordInverse]
  | succ n ih =>
    have hpre : f.stagePaidWordInverse j (n + 1)
        = f.stagePaidWordInverse j n ++ f.stagePaidRoundInverse j := rfl
    have hpre' : f.stagePaidWord j (n + 1)
        = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    have happ : Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration
          (f.stagePaidWordInverse j n ++ f.stagePaidRoundInverse j)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWordInverse j n)
          + Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidRoundInverse j) :=
      weightedCost_append stageDuration (f.stagePaidWordInverse j n)
        (f.stagePaidRoundInverse j)
    have happ' : Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration
          (f.stagePaidRound j ++ f.stagePaidWord j n)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidRound j)
          + Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j n) :=
      weightedCost_append stageDuration (f.stagePaidRound j) (f.stagePaidWord j n)
    have hround : Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidRoundInverse j)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidRound j) := by
      simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost, CoherentVtFrame.stagePaidRoundInverse,
        CoherentVtFrame.stagePaidRound]
    rw [hpre, happ, hpre', happ', hround, ih]
    ring

/-- The coherent variable-time program's access time is the sum of each stage duration
multiplied by its scheduled odd call count. -/
theorem coherentVtProgram_accessTime (f : CoherentVtFrame H m) (rounds : Fin m → ℕ) :
    (f.coherentVtProgram rounds).accessTime stageDuration
      = ((List.finRange m).map
          (fun j => (2 * rounds j + 1) * stageDuration j.val)).sum := by
  unfold VtAmpProgram.accessTime
  rw [show (f.coherentVtProgram rounds).word = f.coherentPaidWord rounds from rfl]
  calc
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.coherentPaidWord rounds)
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration
            ((List.finRange m).map (fun j => f.stagePaidWord j (2 * rounds j + 1))).flatten := rfl
    _ = (((List.finRange m).map (fun j => f.stagePaidWord j (2 * rounds j + 1))).map
          (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration)).sum :=
      weightedCost_flatten stageDuration
        ((List.finRange m).map (fun j => f.stagePaidWord j (2 * rounds j + 1)))
    _ = ((List.finRange m).map
          (fun j => (2 * rounds j + 1) * stageDuration j.val)).sum := by
        have hmap : (List.map (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration)
              (List.map (fun j => f.stagePaidWord j (2 * rounds j + 1))
                (List.finRange m)))
            = (List.map (fun j => (2 * rounds j + 1) * stageDuration j.val)
              (List.finRange m)) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro j _
          exact f.stagePaidWord_accessTime_amp j (rounds j)
        exact congrArg (fun l => l.sum) hmap

/-- The real-valued access time of the coherent variable-time program equals `chargedAccessTime`
for its schedule. -/
theorem coherentVtProgram_accessTime_eq_chargedAccessTime (f : CoherentVtFrame H m)
    (rounds : Fin m → ℕ) :
    ((f.coherentVtProgram rounds).accessTime stageDuration : ℝ) = chargedAccessTime rounds := by
  rw [f.coherentVtProgram_accessTime rounds]
  have hconv := sum_finRange_map_nat m (fun j : Fin m => (2 * rounds j + 1) * stageDuration j.val)
  rw [hconv, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [stageDuration, Nat.cast_mul]

/-- Under schedule agreement, positive base weights, amplified-weight floors, and gain windows,
program access time satisfies the product-sum bound from equation (6) of [Ambainis2012]. -/
theorem coherentVtProgram_accessTime_le_sourceEq6 (f : CoherentVtFrame H m)
    (rounds : Fin m → ℕ) (k : ℕ → ℕ) (rs rs' : ℕ → ℝ)
    (hk : ∀ j : Fin m, k (j.val + 1) = rounds j)
    (hm : 1 ≤ m)
    (hpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < rs' j)
    (hfloor : ∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j)
    (hwin : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * rs' j ≤ rs j) :
    ((f.coherentVtProgram rounds).accessTime stageDuration : ℝ)
      ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct rs rs' 1 (m + 1) * sourceCumulativeTime k 0
          + eq6ProductSum rs rs' m) := by
  rw [f.coherentVtProgram_accessTime_eq_chargedAccessTime rounds]
  exact chargedAccessTime_le_sourceEq6 rounds k rs rs' hk hm hpos hfloor hwin

/-- The matrices of a stage's macro list equal the instruction matrices of its paid word under
the frame's base oracles. -/
theorem stageMacroList_eq_map (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    (f.stageMacroList j n).map VtMacro.matrix
      = (f.stagePaidWord j n).map (CoherentVtFrame.stepMatrixOf f.baseOracles) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : f.stageMacroList j (n + 1) = f.stageMacroRound j ++ f.stageMacroList j n := rfl
    have hpre' : f.stagePaidWord j (n + 1) = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    rw [hpre, hpre', List.map_append, List.map_append, ih]
    rfl

/-- The stage round's matrix list equals the matrix interpretation of its macro round. -/
theorem stageRoundMacros_eq_macroList (f : CoherentVtFrame H m) (j : Fin m) :
    f.stageRoundMacros j = VtMacro.matrixList (f.stageMacroRound j) := rfl

/-- The stage word's matrix list equals the matrix interpretation of its macro list. -/
theorem stageWordMacros_eq_macroList (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    f.stageWordMacros j n = VtMacro.matrixList (f.stageMacroList j n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : f.stageWordMacros j (n + 1) = f.stageRoundMacros j ++ f.stageWordMacros j n := rfl
    have hpre' : f.stageMacroList j (n + 1) = f.stageMacroRound j ++ f.stageMacroList j n := rfl
    rw [hpre, hpre', VtMacro.matrixList_append, stageRoundMacros_eq_macroList, ih]

/-- Each oracle-slot access count in a stage macro list equals the corresponding call count in
its paid word. -/
theorem stageMacroList_accessCount (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) (i : ℕ) :
    VtMacro.accessCount i (f.stageMacroList j n) = Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j n) i := by
  induction n with
  | zero =>
    simp [VtMacro.accessCount, CoherentVtFrame.stageMacroList, Qatlib.Concepts.QlsReadoutSpec.Amplification.calls,
      CoherentVtFrame.stagePaidWord]
  | succ n ih =>
    have hpre : f.stageMacroList j (n + 1) = f.stageMacroRound j ++ f.stageMacroList j n := rfl
    have hpre' : f.stagePaidWord j (n + 1) = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    rw [hpre, hpre', VtMacro.accessCount_append, calls_append, ih]
    have hroundL : VtMacro.accessCount i (f.stageMacroRound j)
        = (if j.val = i then 1 else 0) := by
      simp [VtMacro.accessCount, CoherentVtFrame.stageMacroRound]
    have hroundR : Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidRound j) i
        = (if j.val = i then 1 else 0) := by
      by_cases h : j.val = i
      · subst h
        simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.calls, CoherentVtFrame.stagePaidRound]
      · simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.calls, CoherentVtFrame.stagePaidRound, h]
    rw [hroundL, hroundR]

/-- The flag count of a stage macro list equals the known-gate count of its paid word. -/
theorem stageMacroList_flagCount (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    VtMacro.flagCount (f.stageMacroList j n) = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j n) := by
  induction n with
  | zero =>
    simp [VtMacro.flagCount, CoherentVtFrame.stageMacroList, Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount,
      CoherentVtFrame.stagePaidWord]
  | succ n ih =>
    have hpre : f.stageMacroList j (n + 1) = f.stageMacroRound j ++ f.stageMacroList j n := rfl
    have hpre' : f.stagePaidWord j (n + 1) = f.stagePaidRound j ++ f.stagePaidWord j n := rfl
    rw [hpre, hpre', VtMacro.flagCount_append, gateCount_append, ih]
    have hroundL : VtMacro.flagCount (f.stageMacroRound j) = 2 := by
      simp [VtMacro.flagCount, CoherentVtFrame.stageMacroRound]
    have hroundR : Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidRound j) = 2 := by
      simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount, CoherentVtFrame.stagePaidRound]
    rw [hroundL, hroundR]

/-- A word's matrix equals the reverse-ordered product of its instruction matrices under the
supplied oracles. -/
private theorem wordMatrix_eq_map_stepMatrixOf {H : Type} [Fintype H] [DecidableEq H]
    (oracles : ℕ → Matrix H H ℂ) (C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix oracles C
      = (C.map (CoherentVtFrame.stepMatrixOf oracles)).reverse.prod := by
  unfold Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix
  congr 1
  congr 1
  apply List.map_congr_left
  intro s _
  cases s with
  | known U => rfl
  | call i T adj => rfl

/-- The reverse-ordered product of a stage macro list's matrices equals its paid word's matrix
under the frame's base oracles. -/
theorem stageMacroList_product (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    ((f.stageMacroList j n).map VtMacro.matrix).reverse.prod
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix f.baseOracles (f.stagePaidWord j n) := by
  rw [f.stageMacroList_eq_map j n]
  exact (wordMatrix_eq_map_stepMatrixOf f.baseOracles (f.stagePaidWord j n)).symm

/-- The matrices of an inverse stage macro list equal the instruction matrices of its inverse
paid word under the base oracles. -/
theorem stageMacroListInverse_eq_map (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    (f.stageMacroListInverse j n).map VtMacro.matrix
      = (f.stagePaidWordInverse j n).map (CoherentVtFrame.stepMatrixOf f.baseOracles) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : f.stageMacroListInverse j (n + 1)
        = f.stageMacroListInverse j n ++ f.stageMacroRoundInverse j := rfl
    have hpre' : f.stagePaidWordInverse j (n + 1)
        = f.stagePaidWordInverse j n ++ f.stagePaidRoundInverse j := rfl
    rw [hpre, hpre', List.map_append, List.map_append, ih]
    rfl

/-- Each oracle-slot access count in an inverse stage macro list equals the corresponding call
count in its inverse paid word. -/
theorem stageMacroListInverse_accessCount (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ)
    (i : ℕ) :
    VtMacro.accessCount i (f.stageMacroListInverse j n)
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWordInverse j n) i := by
  induction n with
  | zero =>
    simp [VtMacro.accessCount, CoherentVtFrame.stageMacroListInverse, Qatlib.Concepts.QlsReadoutSpec.Amplification.calls,
      CoherentVtFrame.stagePaidWordInverse]
  | succ n ih =>
    have hpre : f.stageMacroListInverse j (n + 1)
        = f.stageMacroListInverse j n ++ f.stageMacroRoundInverse j := rfl
    have hpre' : f.stagePaidWordInverse j (n + 1)
        = f.stagePaidWordInverse j n ++ f.stagePaidRoundInverse j := rfl
    rw [hpre, hpre', VtMacro.accessCount_append, calls_append, ih]
    have hroundL : VtMacro.accessCount i (f.stageMacroRoundInverse j)
        = (if j.val = i then 1 else 0) := by
      simp [VtMacro.accessCount, CoherentVtFrame.stageMacroRoundInverse]
    have hroundR : Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidRoundInverse j) i
        = (if j.val = i then 1 else 0) := by
      by_cases h : j.val = i
      · subst h
        simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.calls,
            CoherentVtFrame.stagePaidRoundInverse]
      · simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.calls,
          CoherentVtFrame.stagePaidRoundInverse, h]
    rw [hroundL, hroundR]

/-- The flag count of an inverse stage macro list equals the known-gate count of its inverse
paid word. -/
theorem stageMacroListInverse_flagCount (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    VtMacro.flagCount (f.stageMacroListInverse j n)
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWordInverse j n) := by
  induction n with
  | zero =>
    simp [VtMacro.flagCount, CoherentVtFrame.stageMacroListInverse, Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount,
      CoherentVtFrame.stagePaidWordInverse]
  | succ n ih =>
    have hpre : f.stageMacroListInverse j (n + 1)
        = f.stageMacroListInverse j n ++ f.stageMacroRoundInverse j := rfl
    have hpre' : f.stagePaidWordInverse j (n + 1)
        = f.stagePaidWordInverse j n ++ f.stagePaidRoundInverse j := rfl
    rw [hpre, hpre', VtMacro.flagCount_append, gateCount_append, ih]
    have hroundL : VtMacro.flagCount (f.stageMacroRoundInverse j) = 2 := by
      simp [VtMacro.flagCount, CoherentVtFrame.stageMacroRoundInverse]
    have hroundR : Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidRoundInverse j) = 2 := by
      simp [Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount,
          CoherentVtFrame.stagePaidRoundInverse]
    rw [hroundL, hroundR]

/-- The reverse-ordered product of inverse stage macro matrices equals the inverse paid word's
matrix under the base oracles. -/
theorem stageMacroListInverse_product (f : CoherentVtFrame H m) (j : Fin m) (n : ℕ) :
    ((f.stageMacroListInverse j n).map VtMacro.matrix).reverse.prod
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix f.baseOracles (f.stagePaidWordInverse j n) := by
  rw [f.stageMacroListInverse_eq_map j n]
  exact (wordMatrix_eq_map_stepMatrixOf f.baseOracles (f.stagePaidWordInverse j n)).symm

end CoherentVtFrame

/-- For `0 < p ≤ 1` and a round count in the tight amplification window, `tightAASuccess` is
bounded above by the exact squared-sine amplification expression. -/
theorem aaWindow_success {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {m : ℕ}
    (hwin : (m : ℝ) ≤ tightAAWindow p) :
    tightAASuccess p m
      ≤ Real.sin ((2 * (m : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2 := by
  have hwin' : (m : ℝ) ≤ Real.pi / (4 * Real.arcsin (Real.sqrt p)) - 1 / 2 := by
    simpa [tightAAWindow] using! hwin
  have hΘpos : 0 < Real.arcsin (Real.sqrt p) := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp)
  have h4pos : 0 < 4 * Real.arcsin (Real.sqrt p) := by positivity
  have hmoved : (m : ℝ) + 1 / 2 ≤ Real.pi / (4 * Real.arcsin (Real.sqrt p)) := by
    linarith
  have hcross : ((m : ℝ) + 1 / 2) * (4 * Real.arcsin (Real.sqrt p)) ≤ Real.pi :=
    (le_div_iff₀ h4pos).mp hmoved
  have hΘwin : (2 * (m : ℝ) + 1) * Real.arcsin (Real.sqrt p) ≤ Real.pi / 2 := by
    have h : ((m : ℝ) + 1 / 2) * (4 * Real.arcsin (Real.sqrt p))
        = 2 * ((2 * (m : ℝ) + 1) * Real.arcsin (Real.sqrt p)) := by ring
    nlinarith [h, hcross]
  have hsqrt1 : Real.sqrt p ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hsinθ : Real.sin (Real.arcsin (Real.sqrt p)) ^ 2 = p := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) hsqrt1]
    exact Real.sq_sqrt (le_of_lt hp)
  have hcast : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by norm_cast
  have hΘ' : ((2 * m + 1 : ℕ) : ℝ) * Real.arcsin (Real.sqrt p) ≤ Real.pi / 2 := by
    rw [hcast]; exact hΘwin
  have hle := clause88_tight_sin_sq (2 * m + 1) (Real.arcsin (Real.sqrt p))
    (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg p)) (Real.arcsin_le_pi_div_two _) hΘ'
  rw [hsinθ, hcast] at hle
  have hts : tightAASuccess p m
      = (1 - (2 * (m : ℝ) + 1) ^ 2 * p / 3) * ((2 * (m : ℝ) + 1) ^ 2 * p) := by
    simp only [tightAASuccess]
    ring
  rw [hts]
  exact hle

/-- Reaching `aaTarget` with positive base success `p` forces the squared amplification
multiplier times `p` to be at least one, and the squared multiplier to be at least `1 / p`. -/
theorem aaSuccess_target_sq {p : ℝ} (hp : 0 < p) {m : ℕ}
    (htarget : aaTarget ≤ tightAASuccess p m) :
    1 ≤ (aaMultiplier m : ℝ) ^ 2 * p ∧ (aaMultiplier m : ℝ) ^ 2 ≥ 1 / p := by
  have hmult : (aaMultiplier m : ℝ) = 2 * (m : ℝ) + 1 := by
    show (↑(2 * m + 1) : ℝ) = 2 * ↑m + 1
    norm_num
  have hts : tightAASuccess p m
      = (1 - (2 * (m : ℝ) + 1) ^ 2 * p / 3) * ((2 * (m : ℝ) + 1) ^ 2 * p) := by
    simp only [tightAASuccess]
    ring
  set u : ℝ := (2 * (m : ℝ) + 1) ^ 2 * p with hu
  have hpoly : (u - 1) * (u - 2) ≤ 0 := by
    have h : (1 - u / 3) * u ≥ 2 / 3 := by
      rw [← hts]
      simpa [aaTarget] using! htarget
    nlinarith [h]
  have h1 : 1 ≤ u := by
    by_contra hcon
    have hlt : u < 1 := lt_of_not_ge hcon
    have hpos : (u - 1) * (u - 2) > 0 := by
      have h1' : u - 1 < 0 := by linarith
      have h2' : u - 2 < 0 := by linarith
      nlinarith [h1', h2']
    linarith
  have h2 : u ≤ 2 := by
    by_contra hcon
    have hgt : 2 < u := lt_of_not_ge hcon
    have hpos : (u - 1) * (u - 2) > 0 := by
      have h1' : 0 < u - 1 := by linarith
      have h2' : 0 < u - 2 := by linarith
      exact mul_pos h1' h2'
    linarith
  have hlow : 1 ≤ (aaMultiplier m : ℝ) ^ 2 * p := by
    rw [hmult, ← hu]
    exact h1
  have hup : (aaMultiplier m : ℝ) ^ 2 ≥ 1 / p := (div_le_iff₀ hp).mpr hlow
  exact ⟨hlow, hup⟩

/-- If amplification reaches `aaTarget` from positive success `p`, the squared paid stage access
cost is at least the squared stage duration divided by `p`. -/
theorem stagePaidWord_cost_sq (f : CoherentVtFrame H m) (j : Fin m) (m : ℕ) {p : ℝ}
    (hp : 0 < p) (htarget : aaTarget ≤ tightAASuccess p m) :
    (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * m + 1)) : ℝ) ^ 2
      ≥ (1 / p) * (stageDuration j.val : ℝ) ^ 2 := by
  have hcost := f.stagePaidWord_accessTime_amp j m
  have hsq := aaSuccess_target_sq hp htarget
  have hsq' : (2 * (m : ℝ) + 1) ^ 2 ≥ 1 / p := by
    have hmult : (aaMultiplier m : ℝ) = 2 * (m : ℝ) + 1 := by
      show (↑(2 * m + 1) : ℝ) = 2 * ↑m + 1
      norm_num
    rw [hmult] at hsq
    exact (div_le_iff₀ hp).mpr hsq.1
  rw [hcost]
  calc
    (↑((2 * m + 1) * stageDuration j.val) : ℝ) ^ 2
        = (2 * (m : ℝ) + 1) ^ 2 * (stageDuration j.val : ℝ) ^ 2 := by
          rw [Nat.cast_mul]
          have hcast : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by norm_num
          rw [hcast]
          ring
    _ ≥ (1 / p) * (stageDuration j.val : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (stageDuration j.val : ℝ) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hsq' hnonneg
      linarith

/-- Reaching `aaTarget` from positive success `p` requires an amplification multiplier at least
`1 / √p`. -/
theorem aaMultiplier_ge_inv_sqrt {p : ℝ} (hp : 0 < p) {m : ℕ}
    (htarget : aaTarget ≤ tightAASuccess p m) :
    (1 : ℝ) / Real.sqrt p ≤ aaMultiplier m := by
  have hsq := aaSuccess_target_sq hp htarget
  have hsqrtpos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 hp
  have h1 : (aaMultiplier m : ℝ) ^ 2 * p ≥ 1 := by
    have h := (div_le_iff₀ hp).mp hsq.2
    linarith
  have h2 : (0 : ℝ) ≤ aaMultiplier m := by positivity
  have h4 : (0 : ℝ) ≤ (aaMultiplier m : ℝ) * Real.sqrt p :=
    mul_nonneg h2 (le_of_lt hsqrtpos)
  have hsq' : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt (le_of_lt hp)
  have h5 : (aaMultiplier m : ℝ) * Real.sqrt p * (aaMultiplier m : ℝ) * Real.sqrt p
      = (aaMultiplier m : ℝ) ^ 2 * p := by
    calc
      (aaMultiplier m : ℝ) * Real.sqrt p * (aaMultiplier m : ℝ) * Real.sqrt p
          = (aaMultiplier m : ℝ) ^ 2 * (Real.sqrt p) ^ 2 := by ring
      _ = (aaMultiplier m : ℝ) ^ 2 * p := by rw [hsq']
  have h6 : 1 ≤ (aaMultiplier m : ℝ) * Real.sqrt p * (aaMultiplier m : ℝ) * Real.sqrt p := by
    rw [h5]
    exact h1
  have h7 : 1 ≤ (aaMultiplier m : ℝ) * Real.sqrt p := by nlinarith
  rw [div_le_iff₀ hsqrtpos]
  nlinarith

/-- If amplification reaches `aaTarget` from positive success `p`, paid stage access cost is at
least the stage duration divided by `√p`. -/
theorem stagePaidWord_cost_sqrt (f : CoherentVtFrame H m) (j : Fin m) (m : ℕ) {p : ℝ}
    (hp : 0 < p) (htarget : aaTarget ≤ tightAASuccess p m) :
    (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * m + 1)) : ℝ)
      ≥ (1 / Real.sqrt p) * (stageDuration j.val : ℝ) := by
  have hcost := f.stagePaidWord_accessTime_amp j m
  have hmult := aaMultiplier_ge_inv_sqrt hp htarget
  have hD : (0 : ℝ) ≤ (stageDuration j.val : ℝ) := by positivity
  have hcost' : (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * m + 1)) : ℝ)
      = (aaMultiplier m : ℝ) * (stageDuration j.val : ℝ) := by
    rw [hcost, Nat.cast_mul]
    rfl
  calc
    (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * m + 1)) : ℝ)
        = (aaMultiplier m : ℝ) * (stageDuration j.val : ℝ) := hcost'
    _ ≥ (1 / Real.sqrt p) * (stageDuration j.val : ℝ) :=
      mul_le_mul_of_nonneg_right hmult hD

/-- For a positive round count `m`, reaching `aaTarget` from positive base success implies
`tightAASuccess ≥ 1 / (9 * m)`. -/
theorem aaSuccess_ge_source_floor {p : ℝ} (hp : 0 < p) {m : ℕ}
    (htarget : aaTarget ≤ tightAASuccess p m) (hm : 0 < m) :
    1 / (9 * (m : ℝ)) ≤ tightAASuccess p m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 9 ≤ 9 * (m : ℝ) := by linarith
  have h1 : 1 / (9 * (m : ℝ)) ≤ 1 / 9 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hden
  have h2 : (2 / 3 : ℝ) ≤ tightAASuccess p m := by simpa [aaTarget] using! htarget
  linarith

/-- Every schedule satisfies the charged access-time formula, equality with measured program
access time, and the scheduled odd oracle-call counts. -/
theorem schedule_uniform (f : CoherentVtFrame H m) (rounds : Fin m → ℕ) :

    chargedAccessTime rounds = ∑ j : Fin m, (2 * rounds j + 1 : ℝ) * (2 : ℝ) ^ j.val ∧

    ((f.coherentVtProgram rounds).accessTime stageDuration : ℝ)
      = chargedAccessTime rounds ∧

    (∀ j : Fin m, Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j (2 * rounds j + 1)) j.val
      = 2 * rounds j + 1) := by
  refine ⟨rfl, f.coherentVtProgram_accessTime_eq_chargedAccessTime rounds, ?_⟩
  intro j
  exact f.stagePaidWord_calls_amp j (rounds j)

/-- For a policy-selected schedule, charged access time is the sum of policy odd multipliers
times dyadic stage durations. -/
theorem chargedAccessTime_policy (pol : StagePolicy) (measured : Fin m → ℝ) :
    chargedAccessTime (policySchedule pol measured)
      = ∑ j : Fin m, (2 * pol.roundsAt (measured j) + 1 : ℝ) * (2 : ℝ) ^ j.val := by
  simp [chargedAccessTime, policySchedule]

/-- For positive measured stage success, the policy-selected round count lies within the
corresponding tight amplification window. -/
theorem policySchedule_window (pol : StagePolicy) (measured : Fin m → ℝ)
    (hpos : ∀ j, 0 < measured j) (j : Fin m) :
    (policySchedule pol measured j : ℝ) ≤ tightAAWindow (measured j) :=
  pol.roundsAt_window _ (hpos j)

/-- A positive policy round count reaching `aaTarget` yields the success floor,
squared-multiplier lower bound, and squared paid stage-cost lower bound at that stage. -/
theorem policy_stage_data (f : CoherentVtFrame H m) (pol : StagePolicy)
    (measured : Fin m → ℝ) (j : Fin m) (hpos : 0 < measured j)
    (htarget : aaTarget ≤ tightAASuccess (measured j) (pol.roundsAt (measured j)))
    (hround : 0 < pol.roundsAt (measured j)) :
    (1 / (9 * (pol.roundsAt (measured j) : ℝ)))
        ≤ tightAASuccess (measured j) (pol.roundsAt (measured j)) ∧
    1 ≤ (aaMultiplier (pol.roundsAt (measured j)) : ℝ) ^ 2 * measured j ∧
    (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration
        (f.stagePaidWord j (2 * pol.roundsAt (measured j) + 1)) : ℝ) ^ 2
      ≥ (1 / measured j) * (stageDuration j.val : ℝ) ^ 2 := by
  refine ⟨aaSuccess_ge_source_floor hpos htarget hround, (aaSuccess_target_sq hpos htarget).1,
    stagePaidWord_cost_sq f j (pol.roundsAt (measured j)) hpos htarget⟩

/-- A policy-selected schedule satisfying the weight positivity, floor, and gain-window
assumptions obeys the corrected product-sum access-time bound of [Ambainis, equation
(6)][Ambainis2012]. -/
theorem chargedAccessTime_le_sourceEq6_policy (pol : StagePolicy)
    (measured : Fin m → ℝ) (k : ℕ → ℕ) (rs rs' : ℕ → ℝ)
    (hk : ∀ j : Fin m, k (j.val + 1) = pol.roundsAt (measured j))
    (hm : 1 ≤ m)
    (hpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < rs' j)
    (hfloor : ∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j)
    (hwin : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * rs' j ≤ rs j) :
    chargedAccessTime (policySchedule pol measured)
      ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct rs rs' 1 (m + 1) * sourceCumulativeTime k 0
          + eq6ProductSum rs rs' m) := by
  exact chargedAccessTime_le_sourceEq6 (policySchedule pol measured) k rs rs' hk hm hpos hfloor hwin

/-- The measured access time of the coherent program using a policy schedule equals that
schedule's charged access time. -/
theorem coherentVtProgram_accessTime_policy (f : CoherentVtFrame H m)
    (pol : StagePolicy) (measured : Fin m → ℝ) :
    ((f.coherentVtProgram (policySchedule pol measured)).accessTime stageDuration : ℝ)
      = chargedAccessTime (policySchedule pol measured) :=
  f.coherentVtProgram_accessTime_eq_chargedAccessTime _

/-- The gain ratio of measured amplified and base stage successes is the ratio of their square
roots. -/
theorem gainRatio_measured (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    gainRatio (ampStageSuccess f ψ j) (baseStageSuccess f ψ j)
      = Real.sqrt (ampStageSuccess f ψ j) / Real.sqrt (baseStageSuccess f ψ j) := rfl

/-- Measured base and amplified stage success masses are both nonnegative. -/
theorem measured_stage_success_bounds (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    0 ≤ baseStageSuccess f ψ j ∧ 0 ≤ ampStageSuccess f ψ j := by
  refine ⟨measureProb_nonneg _ _, measureProb_nonneg _ _⟩

/-- When measured stage successes satisfy positivity, floor, and gain-window assumptions, the
coherent program's access time obeys the source equation (6) product-sum bound
[Ambainis2012]. -/
theorem chargedAccessTime_le_sourceEq6_measured (f : CoherentVtFrame H m)
    (ψ : QState H) (rounds : Fin m → ℕ) (k : ℕ → ℕ)
    (hk : ∀ j : Fin m, k (j.val + 1) = rounds j) (hm : 1 ≤ m)
    (hpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < measuredRs' f ψ j)
    (hfloor : ∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ measuredRs f ψ j)
    (hwin : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * measuredRs' f ψ j
        ≤ measuredRs f ψ j) :
    ((f.coherentVtProgram rounds).accessTime stageDuration : ℝ)
      ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct (measuredRs f ψ) (measuredRs' f ψ) 1 (m + 1)
          * sourceCumulativeTime k 0
          + eq6ProductSum (measuredRs f ψ) (measuredRs' f ψ) m) := by
  rw [f.coherentVtProgram_accessTime_eq_chargedAccessTime rounds]
  exact chargedAccessTime_le_sourceEq6 rounds k (measuredRs f ψ) (measuredRs' f ψ)
    hk hm hpos hfloor hwin

/-- Expands the tight access-cost expression at the frame's positive final success into the
maximum-time and average-time terms of [Ambainis, Theorem 1][Ambainis2012]. -/
theorem sourceTheorem1_constant (f : CoherentVtFrame H m) (ψ : QState H)
    (hp : 0 < CoherentVtFrame.runSuccess f ψ) :
    tightAccessCost (maxStopTime m)
        (averageStopTime m (fun j => f.freshStopMass ψ j)) (CoherentVtFrame.runSuccess f ψ)
      = maxStopTime m * Real.sqrt (tightLogFactor (maxStopTime m))
        + averageStopTime m (fun j => f.freshStopMass ψ j)
          * (tightLogFactor (maxStopTime m)) ^ ((3 : ℝ) / 2)
          / Real.sqrt (CoherentVtFrame.runSuccess f ψ) :=
  sourceAccessConstant f ψ (CoherentVtFrame.runSuccess f ψ) hp

/-- Combines the measured equation (6) access-time bound with the explicit tight access-cost
identity associated with [Ambainis, Theorem 1][Ambainis2012], under the stated gain and
success assumptions. -/
theorem sourceTheorem1_measured (f : CoherentVtFrame H m) (ψ : QState H)
    (rounds : Fin m → ℕ) (k : ℕ → ℕ)
    (hk : ∀ j : Fin m, k (j.val + 1) = rounds j) (hm : 1 ≤ m)
    (hpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < measuredRs' f ψ j)
    (hfloor : ∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ measuredRs f ψ j)
    (hwin : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * measuredRs' f ψ j
        ≤ measuredRs f ψ j)
    (hp : 0 < CoherentVtFrame.runSuccess f ψ) :
    ((f.coherentVtProgram rounds).accessTime stageDuration : ℝ)
      ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct (measuredRs f ψ) (measuredRs' f ψ) 1 (m + 1)
          * sourceCumulativeTime k 0
          + eq6ProductSum (measuredRs f ψ) (measuredRs' f ψ) m) ∧
    tightAccessCost (maxStopTime m)
        (averageStopTime m (fun j => f.freshStopMass ψ j)) (CoherentVtFrame.runSuccess f ψ)
      = maxStopTime m * Real.sqrt (tightLogFactor (maxStopTime m))
        + averageStopTime m (fun j => f.freshStopMass ψ j)
          * (tightLogFactor (maxStopTime m)) ^ ((3 : ℝ) / 2)
          / Real.sqrt (CoherentVtFrame.runSuccess f ψ) := by
  refine ⟨chargedAccessTime_le_sourceEq6_measured f ψ rounds k hk hm hpos hfloor hwin,
    sourceTheorem1_constant f ψ hp⟩

/-- Collects unitarity, stopped-history preservation, fresh-projector orthogonality,
stage-record transitions, execution semantics, and frozen/running fragment identities for a
coherent frame. -/
theorem clause1_endpoint (f : CoherentVtFrame H m) (ψ : QState H) :
    IsUnitaryCircuit (f.coherentProgram) ∧
    f.totalOp ∈ Matrix.unitaryGroup H ℂ ∧
    (∀ j : Fin m, f.stageOp j ∈ Matrix.unitaryGroup H ℂ ∧
      f.stageOp j * f.stopAt j = f.stopAt j ∧ f.stopAt j * f.stageOp j = f.stopAt j) ∧
    (∀ j : Fin m, IsOrthogonalProjector (f.freshStop j) ∧
      f.stopAt j * f.freshStop j = 0 ∧ f.freshStop j * f.stopAt j = 0) ∧
    (∀ j : Fin m, 0 ≤ f.freshStopMass ψ j) ∧
    (∀ j k : Fin m, k.val < j.val → f.freshStop k * f.freshStop j = 0) ∧
    (∀ j : Fin m,
      f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ = f.stopAt j + f.freshStop j) ∧
    (∀ j : Fin m,
      (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.stageOp j
        = (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) * f.round j) ∧
    (∀ (n : ℕ) (h : n + 1 ≤ m),
      f.stageState ψ (n + 1) h
        = ApplyGate (f.stageOp ⟨n, Nat.lt_of_succ_le h⟩) (f.stageState ψ n (Nat.le_of_succ_le h))) ∧
    (∀ j : Fin m,
      ApplyGate (f.stageOp j) (f.stageRecord ψ j).inputState
        = (f.stageRecord ψ j).outputState) ∧
    (∀ j : Fin m,
      (f.stageRecord ψ j).reachedStop = f.stopAt j + (f.stageRecord ψ j).freshStop) ∧
    (∀ j k : Fin m, j.val ≤ k.val → f.stopAt j * f.stageOp k = f.stopAt j) ∧

    Run 1 (f.coherentProgram) ψ = f.stageState ψ m (by omega) ∧
    ApplyGate (f.totalOp) ψ = f.stageState ψ m (by omega) ∧

    (∀ j : Fin m,
      f.frozenFragment (f.stageState ψ (j.val + 1) (by omega)) j
        + f.runningFragment (f.stageState ψ (j.val + 1) (by omega)) j
        = f.stageState ψ (j.val + 1) (by omega)) ∧
    (∀ j : Fin m,
      ApplyGate (f.stopAt j) (f.runningFragment ψ j) = 0 ∧
      ApplyGate (1 - f.stopAt j) (f.frozenFragment ψ j) = 0) ∧

    (∀ j k : Fin m, j.val ≤ k.val →
      f.frozenFragment (f.stageState ψ k.val (by omega)) j
        = f.frozenFragment (f.stageState ψ j.val (by omega)) j) ∧

    (∀ j : Fin m,
      f.runningFragmentAfter (f.stageState ψ (j.val + 1) (by omega)) j
        = f.runningFragmentAfter
            (ApplyGate (f.round j) (f.stageState ψ j.val (by omega))) j) := by
  refine ⟨f.coherentProgram_unitary, f.totalOp_unitary, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    f.coherentProgram_run_eq ψ, f.totalOp_apply_eq_stageState ψ, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨f.stageOp_unitary j, f.stageOp_mul_stop j, f.stop_mul_stageOp j⟩
  · intro j
    exact ⟨f.freshStop_orth j, (f.freshStop_orthogonal j).1, (f.freshStop_orthogonal j).2⟩
  · intro j
    exact f.freshStopMass_nonneg ψ j
  · intro j k hjk
    exact f.freshStop_disjoint j k hjk
  · intro j
    exact f.stopHistory_split j
  · intro j
    exact f.runningPart_step j
  · intro n h
    exact f.stageState_succ ψ n h
  · intro j
    exact f.stageRecord_transition ψ j
  · intro j
    exact f.stageRecord_reachedStop_split ψ j
  · intro j k hjk
    exact f.stop_mul_stageOp_later j k hjk
  · intro j
    exact f.stageState_frozen_running ψ j
  · intro j
    exact f.frozen_running_orthogonal ψ j
  · intro j k hjk
    exact f.frozenFragment_frozen ψ j k hjk
  · intro j
    exact f.runningFragment_transported ψ j

/-- Collects stage-circuit matrix semantics, forward and inverse access counts, reflection
counts, access times, and agreement between paid-word and macro interpretations. -/
theorem clause2_endpoint (f : CoherentVtFrame H m) (j : Fin m) (k : ℕ) :
    IsUnitaryCircuit (f.stageWord j) ∧
    f.stageWordMatrix j = f.round j ∧
    f.stageWordInverseMatrix j = (f.round j)ᴴ ∧
    stageTime j.val k = stageVisitCount k * stageVisitTime j.val ∧
    stageVisitTime j.val = 2 ^ j.val ∧
    stageInverseTime j.val k = stageTime j.val k ∧
    stageFlagReflections k = 2 * stageVisitCount k ∧
    stageInverseQueryCount k = stageQueryCount k ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j (2 * k + 1)) j.val = 2 * k + 1 ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j (2 * k + 1)) = 2 * (2 * k + 1) ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * k + 1))
      = (2 * k + 1) * stageDuration j.val ∧
    f.stagePaidWordInverse j (2 * k + 1)
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint (f.stagePaidWord j (2 * k + 1)) ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix f.baseOracles (f.stagePaidWordInverse j (2 * k + 1))
      = (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix f.baseOracles (f.stagePaidWord j (2 * k + 1)))ᴴ ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWordInverse j (2 * k + 1)) j.val
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j (2 * k + 1)) j.val ∧

    (f.stageMacroList j (2 * k + 1)).map VtMacro.matrix
      = (f.stagePaidWord j (2 * k + 1)).map (CoherentVtFrame.stepMatrixOf f.baseOracles) ∧

    (∀ i : ℕ, VtMacro.accessCount i (f.stageMacroList j (2 * k + 1))
        = Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j (2 * k + 1)) i) ∧
    VtMacro.flagCount (f.stageMacroList j (2 * k + 1))
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j (2 * k + 1)) ∧

    ((f.stageMacroList j (2 * k + 1)).map VtMacro.matrix).reverse.prod
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix f.baseOracles (f.stagePaidWord j (2 * k + 1)) ∧
    ((f.stageMacroListInverse j (2 * k + 1)).map VtMacro.matrix).reverse.prod
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix f.baseOracles (f.stagePaidWordInverse j (2 * k + 1)) ∧
    VtMacro.flagCount (f.stageMacroListInverse j (2 * k + 1))
      = Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWordInverse j (2 * k + 1)) := by
  refine ⟨?_, f.stageWordMatrix_eq j, f.stageWordInverseMatrix_eq j,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    simp [CoherentVtFrame.stageWord] at hU
    rcases hU with hU | hU | hU
    · have hU' : U = targetMark f.target := by simpa only [Step.gate.injEq] using! hU
      rw [hU']
      exact targetMark_unitary f.targetOrth
    · have hU' : U = f.base j := by simpa only [Step.gate.injEq] using! hU
      rw [hU']
      exact f.baseUnitary j
    · have hU' : U = targetMark f.target := by simpa only [Step.gate.injEq] using! hU
      rw [hU']
      exact targetMark_unitary f.targetOrth
  · rfl
  · rfl
  · rfl
  · exact stageFlagReflections_eq k
  · rfl
  · exact f.stagePaidWord_calls_amp j k
  · exact f.stagePaidWord_gateCount j (2 * k + 1)
  · exact f.stagePaidWord_accessTime_amp j k
  · exact f.stagePaidWordInverse_eq_wordAdjoint j (2 * k + 1)
  · exact f.stagePaidWord_matrix_adjoint j (2 * k + 1) f.baseOracles
  · exact f.stagePaidWordInverse_calls j (2 * k + 1)
  · exact f.stageMacroList_eq_map j (2 * k + 1)
  · intro i
    exact f.stageMacroList_accessCount j (2 * k + 1) i
  · exact f.stageMacroList_flagCount j (2 * k + 1)
  · exact f.stageMacroList_product j (2 * k + 1)
  · exact ⟨f.stageMacroListInverse_product j (2 * k + 1),
      f.stageMacroListInverse_flagCount j (2 * k + 1)⟩

/-- Collects stopping-time second-moment bounds, adaptive bound comparisons,
amplification-window inequalities, and lower bounds on paid stage costs under the stated
probability and estimate assumptions. -/
theorem clause3_endpoint (f : CoherentVtFrame H m) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hsum : (∑ j : Fin m, q j) ≤ 1) (p : ℝ) (hp : 0 < p)
    (c qhat : ℝ) (hacc : estimateAccurate c p qhat) (B : ℝ) (hB : maxStopTime m ≤ B) :
    stopSecondMoment m q = (averageStopTime m q) ^ 2 ∧
    stopSecondMoment m q ≤ maxStopTime m * averageStopTime m q ∧
    amplifiedSecondMoment q p ≤ meanSquareBound m (averageStopTime m q) p ∧
    stopSecondMoment m q / p ≤ adaptiveMeanSquareBound B (averageStopTime m q) p ∧

    (aaRounds p : ℝ) ≤ tightAAWindow p ∧
    (∀ m' : ℕ, p ≤ 1 → (m' : ℝ) ≤ tightAAWindow p →
      tightAASuccess p m'
        ≤ Real.sin ((2 * (m' : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2) ∧

    (∀ m' : ℕ, aaTarget ≤ tightAASuccess p m' →
      1 ≤ (aaMultiplier m' : ℝ) ^ 2 * p ∧ (aaMultiplier m' : ℝ) ^ 2 ≥ 1 / p) ∧

    (∀ (j : Fin m) (m' : ℕ), aaTarget ≤ tightAASuccess p m' →
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost stageDuration (f.stagePaidWord j (2 * m' + 1)) : ℝ) ^ 2
        ≥ (1 / p) * (stageDuration j.val : ℝ) ^ 2) ∧

    meanSquareBound m (averageStopTime m q) p
      ≤ adaptiveMeanSquareBound B (averageStopTime m q) p ∧

    (∀ (c' qhat' : ℝ), estimateAccurate c' p qhat' →
      stopSecondMoment m q / p ≤ adaptiveMeanSquareBound B (averageStopTime m q) p) ∧

    (∀ (k qmeas : ℝ), 0 ≤ k → 0 ≤ qmeas → p ≤ 1 →
      adaptiveMeanSquareBound B (averageStopTime m q) p
        ≤ adaptiveTotalBound k B (averageStopTime m q) p qmeas) := by
  refine ⟨stopSecondMoment_eq_averageSq q hq, stopSecondMoment_le_max_mul_average q hq hsum,
    amplified_stopSecondMoment_le q hq hsum p hp,
    adaptive_stopSecondMoment_le q hq hsum p hp c qhat hacc B hB,
    aaRounds_window hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m' hp1 hwin
    exact aaWindow_success hp hp1 hwin
  · intro m' htarget
    exact aaSuccess_target_sq hp htarget
  · intro j m' htarget
    exact stagePaidWord_cost_sq f j m' hp htarget
  · exact meanSquareBound_le_adaptiveBound m (averageStopTime m q) p B hB
      (Real.sqrt_nonneg _) hp
  · intro c' qhat' hacc'
    exact adaptive_stopSecondMoment_le q hq hsum p hp c' qhat' hacc' B hB
  · intro k qmeas hk hqmeas hp1
    exact adaptiveTotalBound_ge hk hp hp1 hqmeas

/-- For normalized input and a base success in `(0, 1)`, the rotation-window hypothesis bounds
actual amplified stage success below by `tightAASuccess`, as in [Ambainis, Lemma
1][Ambainis2012]. -/
theorem sourceStage_lemma1 (f : CoherentVtFrame H m) {ψ : QState H} (hψ : Normalized ψ)
    (j : Fin m) (k : ℕ)
    (hδ0 : 0 < f.sourceBaseSuccess ψ j) (hδ1 : f.sourceBaseSuccess ψ j < 1)
    (hwin : ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt (f.sourceBaseSuccess ψ j))
      ≤ Real.pi / 2) :
    tightAASuccess (f.sourceBaseSuccess ψ j) k ≤ f.sourceAmpSuccess ψ j k := by
  have h := source_lemma1 f.targetOrth (normalized_sourcePrepared f hψ j)
    (f.sourceBaseSuccess ψ j) k hδ0 hδ1 hwin rfl
  exact h

/-- For normalized input, a base success in `(0, 1)`, and the source amplification and rotation
windows, actual success is at least `1 - 1 / (3 * m)` times the ideal gain [Ambainis2012]. -/
theorem sourceStage_lemma2_window (f : CoherentVtFrame H m) (hm : 1 ≤ m) {ψ : QState H}
    (hψ : Normalized ψ) (j : Fin m) (k : ℕ)
    (hδ0 : 0 < f.sourceBaseSuccess ψ j) (hδ1 : f.sourceBaseSuccess ψ j < 1)
    (hwin : sourceAlg2Window m k (f.sourceBaseSuccess ψ j))
    (hrot : ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt (f.sourceBaseSuccess ψ j))
      ≤ Real.pi / 2) :
    (1 - 1 / (3 * (m : ℝ))) * sourceIdealGain k (f.sourceBaseSuccess ψ j)
      ≤ f.sourceAmpSuccess ψ j k := by
  have hbound := sourceStage_lemma1 f hψ j k hδ0 hδ1 hrot
  exact source_lemma2_window hm hwin hbound

/-- For normalized input and a base success in `(0, 1)`, the rotation window and the stated
corrected-gain floor imply amplified success at least `1 / (9 * m)`. -/
theorem sourceStage_success_floor (f : CoherentVtFrame H m) (hm : 1 ≤ m) {ψ : QState H}
    (hψ : Normalized ψ) (j : Fin m) (k : ℕ)
    (hδ0 : 0 < f.sourceBaseSuccess ψ j) (hδ1 : f.sourceBaseSuccess ψ j < 1)
    (hrot : ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt (f.sourceBaseSuccess ψ j))
      ≤ Real.pi / 2)
    (hfloor : (1 - (2 * (k : ℝ) + 1) ^ 2 * f.sourceBaseSuccess ψ j / 3)
        * sourceIdealGain k (f.sourceBaseSuccess ψ j) ≥ 1 / (9 * (m : ℝ))) :
    1 / (9 * (m : ℝ)) ≤ f.sourceAmpSuccess ψ j k := by
  have hbound := sourceStage_lemma1 f hψ j k hδ0 hδ1 hrot
  exact source_success_floor hfloor hbound

/-- For a small positive base success and normalized input, a source Algorithm 2 policy selects
a valid window and achieves the stated corrected ideal-gain lower bound [Ambainis2012]. -/
theorem sourceStage_alg2 (f : CoherentVtFrame H m) (hm : 1 ≤ m) (pol : SourceAlg2Policy m)
    {ψ : QState H} (hψ : Normalized ψ) (j : Fin m)
    (hδ0 : 0 < f.sourceBaseSuccess ψ j) (hδ1 : f.sourceBaseSuccess ψ j < 1)
    (hamp : f.sourceBaseSuccess ψ j ≤ 1 / (9 * (m : ℝ))) :
    sourceAlg2Window m (pol.roundsAt (f.sourceBaseSuccess ψ j)) (f.sourceBaseSuccess ψ j)
      ∧ (1 - 1 / (3 * (m : ℝ)))
        * sourceIdealGain (pol.roundsAt (f.sourceBaseSuccess ψ j)) (f.sourceBaseSuccess ψ j)
        ≤ f.sourceAmpSuccess ψ j (pol.roundsAt (f.sourceBaseSuccess ψ j)) := by
  have hwin := pol.roundsAt_window (f.sourceBaseSuccess ψ j) hδ0 hamp
  have hrot := source_rotation_window hm hδ0 hwin.2
  have hlemma1 := sourceStage_lemma1 f hψ j (pol.roundsAt (f.sourceBaseSuccess ψ j))
    hδ0 hδ1 hrot
  exact ⟨hwin, source_lemma2_window hm hwin hlemma1⟩

/-- For `m ≥ 1` and base success in `(0, 1 / (9 * m)]`, `alg2Rounds` satisfies the source
Algorithm 2 window condition [Ambainis2012]. -/
theorem sourceStage_alg2_rule (f : CoherentVtFrame H m) (hm : 1 ≤ m) {ψ : QState H}
    (j : Fin m) (hδ0 : 0 < f.sourceBaseSuccess ψ j)
    (hamp : f.sourceBaseSuccess ψ j ≤ 1 / (9 * (m : ℝ))) :
    sourceAlg2Window m (alg2Rounds m (f.sourceBaseSuccess ψ j)) (f.sourceBaseSuccess ψ j) :=
  alg2Rounds_window hm hδ0 hamp

/-- For `m ≥ 1` and base success in `(0, 1 / (9 * m)]`, the `alg2Rounds` choice keeps the
amplified rotation angle at most `π / 2` [Ambainis2012]. -/
theorem sourceStage_alg2_rule_lemma1 (f : CoherentVtFrame H m) (hm : 1 ≤ m) {ψ : QState H}
    (j : Fin m) (hδ0 : 0 < f.sourceBaseSuccess ψ j)
    (hamp : f.sourceBaseSuccess ψ j ≤ 1 / (9 * (m : ℝ))) :
    ((2 * (alg2Rounds m (f.sourceBaseSuccess ψ j) : ℝ) + 1))
      * Real.arcsin (Real.sqrt (f.sourceBaseSuccess ψ j)) ≤ Real.pi / 2 :=
  alg2Rounds_lemma1_window hm hδ0 hamp

/-- For normalized input and a base success in `(0, 1)`, the rotation and Algorithm 2 windows
together with the ideal-gain threshold imply amplified success at least `1 / (9 * m)`. -/
theorem sourceStage_success_floor_sharp (f : CoherentVtFrame H m) (hm : 1 ≤ m) {ψ : QState H}
    (hψ : Normalized ψ) (j : Fin m) (k : ℕ)
    (hδ0 : 0 < f.sourceBaseSuccess ψ j) (hδ1 : f.sourceBaseSuccess ψ j < 1)
    (hrot : ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt (f.sourceBaseSuccess ψ j))
      ≤ Real.pi / 2)
    (hwin : sourceAlg2Window m k (f.sourceBaseSuccess ψ j))
    (hclear : sourceIdealGain k (f.sourceBaseSuccess ψ j) ≥ sourceFloorThreshold m) :
    1 / (9 * (m : ℝ)) ≤ f.sourceAmpSuccess ψ j k := by
  have hlemma1 := sourceStage_lemma1 f hψ j k hδ0 hδ1 hrot
  have hts : tightAASuccess (f.sourceBaseSuccess ψ j) k
      = (1 - (2 * (k : ℝ) + 1) ^ 2 * f.sourceBaseSuccess ψ j / 3)
        * sourceIdealGain k (f.sourceBaseSuccess ψ j) := by
    simp only [tightAASuccess, sourceIdealGain]
    ring
  have hG : sourceIdealGain k (f.sourceBaseSuccess ψ j)
      * (1 - sourceIdealGain k (f.sourceBaseSuccess ψ j) / 3) ≥ 1 / (9 * (m : ℝ)) :=
    (source_floor_iff hm hwin.2).2 hclear
  have hbound : (1 - (2 * (k : ℝ) + 1) ^ 2 * f.sourceBaseSuccess ψ j / 3)
      * sourceIdealGain k (f.sourceBaseSuccess ψ j) ≥ 1 / (9 * (m : ℝ)) := by
    have hid : (1 - (2 * (k : ℝ) + 1) ^ 2 * f.sourceBaseSuccess ψ j / 3)
        * sourceIdealGain k (f.sourceBaseSuccess ψ j)
        = sourceIdealGain k (f.sourceBaseSuccess ψ j)
          * (1 - sourceIdealGain k (f.sourceBaseSuccess ψ j) / 3) := by
      rw [sourceIdealGain]
      ring
    rw [hid]
    exact hG
  rw [hts] at hlemma1
  exact le_trans hbound hlemma1

/-- For normalized input and positive base success, zero amplification rounds preserve base
success and satisfy the corrected ideal-gain lower bound when `m ≥ 1`. -/
theorem sourceStage_lemma2_window_unamplified (f : CoherentVtFrame H m) (hm : 1 ≤ m)
    {ψ : QState H} (hψ : Normalized ψ) (j : Fin m)
    (hδ0 : 0 < f.sourceBaseSuccess ψ j) :
    f.sourceAmpSuccess ψ j 0 = f.sourceBaseSuccess ψ j ∧
      (1 - 1 / (3 * (m : ℝ))) * sourceIdealGain 0 (f.sourceBaseSuccess ψ j)
        ≤ f.sourceAmpSuccess ψ j 0 := by
  have h : f.sourceAmplified ψ j 0 = f.sourcePrepared ψ j := by
    simp [CoherentVtFrame.sourceAmplified]
  constructor
  · unfold CoherentVtFrame.sourceAmpSuccess
    rw [h]
    rfl
  · unfold CoherentVtFrame.sourceAmpSuccess
    rw [h]
    have hnonneg : 0 ≤ f.sourceBaseSuccess ψ j := sourceBaseSuccess_nonneg f ψ j
    have hfac : 1 - 1 / (3 * (m : ℝ)) ≤ 1 := by
      have : 0 ≤ 1 / (3 * (m : ℝ)) := by positivity
      linarith
    have hmul : (1 - 1 / (3 * (m : ℝ))) * f.sourceBaseSuccess ψ j
        ≤ 1 * f.sourceBaseSuccess ψ j := mul_le_mul_of_nonneg_right hfac hnonneg
    have hid : sourceIdealGain 0 (f.sourceBaseSuccess ψ j) = f.sourceBaseSuccess ψ j := by
      simp [sourceIdealGain]
    rw [hid]
    simpa using! hmul

namespace CoherentVtFrame

variable {m : ℕ}

/-- The ordered product of operators `f.stopAt j + (1 - f.stopAt j) * f.round j`, separating
stopped and running evolution at each stage. -/
def vtEvolution (f : CoherentVtFrame H m) : Matrix H H ℂ :=
  listTotalOp ((List.finRange m).map (fun j => f.stopAt j + (1 - f.stopAt j) * f.round j))

/-- The product of all stage operators equals the evolution matrix expressed by stopped and
running projectors. -/
theorem totalOp_eq_vtEvolution (f : CoherentVtFrame H m) :
    f.totalOp = f.vtEvolution := by
  have h : (List.finRange m).map (fun j : Fin m => f.stageOp j)
      = (List.finRange m).map
          (fun j : Fin m => f.stopAt j + (1 - f.stopAt j) * f.round j) :=
    List.map_congr_left (fun j _ => rfl)
  unfold totalOp vtEvolution
  rw [h]

end CoherentVtFrame

/-- Running the coherent program equals applying the evolution matrix expressed by stopped and
running projectors. -/
theorem coherentProgram_run_eq_vtEvolution (f : CoherentVtFrame H m) (ψ : QState H) :
    Run 1 (f.coherentProgram) ψ = ApplyGate (f.vtEvolution) ψ := by
  rw [f.coherentProgram_run_eq, ← f.totalOp_eq_vtEvolution, f.totalOp_apply_eq_stageState]

/-- The final evolution retains every earlier stopped projection, equal to its value at the
corresponding prefix. -/
theorem totalOp_retains_stopHistory (f : CoherentVtFrame H m) (ψ : QState H)
    (j : Fin m) :
    ApplyGate (f.stopAt j) (ApplyGate (f.totalOp) ψ)
      = ApplyGate (f.stopAt j) (f.stageState ψ j.val (by omega)) := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ m' =>
    rw [f.totalOp_apply_eq_stageState]
    have hlast : f.stageState ψ (m' + 1) (by omega)
        = ApplyGate (f.stageOp ⟨m', by omega⟩) (f.stageState ψ m' (by omega)) := by
      exact f.stageState_succ ψ m' (by omega)
    have hjle : j.val ≤ m' := by omega
    rw [hlast, ← applyGate_mul, f.stop_mul_stageOp_later j ⟨m', by omega⟩ hjle]
    exact f.frozenFragment_frozen ψ j ⟨m', by omega⟩ hjle

/-- The success amplitude and success mass are nonnegative, and both success mass and total
fresh stopping mass are bounded by the input state's total mass. -/
theorem clause1_mass_accounting (f : CoherentVtFrame H m) (ψ : QState H) :
    0 ≤ successAmplitude f ψ ∧
    0 ≤ f.runSuccess ψ ∧
    f.runSuccess ψ ≤ MeasureProb ψ Finset.univ ∧
    (∑ j : Fin m, f.freshStopMass ψ j) ≤ MeasureProb ψ Finset.univ := by
  have hamp : 0 ≤ successAmplitude f ψ := successAmplitude_nonneg f ψ
  have hrun : 0 ≤ f.runSuccess ψ := by
    unfold CoherentVtFrame.runSuccess
    exact measureProb_nonneg _ _
  have hrun1 : f.runSuccess ψ ≤ MeasureProb ψ Finset.univ := f.runSuccess_le_stateMass ψ
  have hstop : (∑ j : Fin m, f.freshStopMass ψ j) ≤ MeasureProb ψ Finset.univ :=
    f.freshStopMass_total_le ψ
  exact ⟨hamp, hrun, hrun1, hstop⟩

/-- Under positive success amplitude and positive policy measurements, collects the evolution
identity, unitarity, stopped-history preservation, mass bounds, and policy window and
access-time formulas. -/
theorem clause1_endpoint_vtEvolution (f : CoherentVtFrame H m) (ψ : QState H)
    (a : ℝ) (ha : a = successAmplitude f ψ) (ha0 : 0 < a)
    (pol : StagePolicy) (measured : Fin m → ℝ) (hmeas : ∀ j, 0 < measured j) :
    f.totalOp = f.vtEvolution ∧
    f.totalOp ∈ Matrix.unitaryGroup H ℂ ∧
    (∀ j : Fin m, ApplyGate (f.stopAt j) (ApplyGate (f.totalOp) ψ)
        = ApplyGate (f.stopAt j) (f.stageState ψ j.val (by omega))) ∧
    (∀ j : Fin m, f.stageOp j * f.stopAt j = f.stopAt j) ∧
    (∀ j k : Fin m, j.val ≤ k.val → f.stopAt j * f.stageOp k = f.stopAt j) ∧

    0 < a ∧ 0 ≤ successAmplitude f ψ ∧

    0 ≤ f.runSuccess ψ ∧
    f.runSuccess ψ ≤ MeasureProb ψ Finset.univ ∧
    (∑ j : Fin m, f.freshStopMass ψ j) ≤ MeasureProb ψ Finset.univ ∧

    (∀ j : Fin m, (policySchedule pol measured j : ℝ)
        ≤ tightAAWindow (measured j)) ∧
    chargedAccessTime (policySchedule pol measured)
      = ∑ j : Fin m, (2 * pol.roundsAt (measured j) + 1 : ℝ) * (2 : ℝ) ^ j.val := by
  refine ⟨f.totalOp_eq_vtEvolution, f.totalOp_unitary, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact totalOp_retains_stopHistory f ψ j
  · intro j
    exact f.stageOp_mul_stop j
  · intro j k hjk
    exact f.stop_mul_stageOp_later j k hjk
  · exact ha0
  · exact successAmplitude_nonneg f ψ
  · have h := f.runSuccess_nonneg ψ
    exact h
  · exact f.runSuccess_le_stateMass ψ
  · exact f.freshStopMass_total_le ψ
  · intro j
    exact policySchedule_window pol measured hmeas j
  · exact chargedAccessTime_policy pol measured

namespace CoherentVtFrame

variable {m : ℕ}

/-- The adjoint stage operator splits into the stopped projector plus the complementary
projector multiplied by the adjoint round matrix. -/
theorem stageOp_adjoint (f : CoherentVtFrame H m) (j : Fin m) :
    (f.stageOp j)ᴴ = f.stopAt j + (1 - f.stopAt j) * (f.round j)ᴴ := by
  have hstar : (f.stopAt j)ᴴ = f.stopAt j := by
    have h := (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).2
    simpa only [Matrix.star_eq_conjTranspose] using! h
  have hcompl : (1 - f.stopAt j)ᴴ = 1 - f.stopAt j := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar]
  have hcomm : f.round j * f.stopAt j = f.stopAt j * f.round j := f.round_comm j
  have hcomm' : (f.round j)ᴴ * f.stopAt j = f.stopAt j * (f.round j)ᴴ := by
    have h := congrArg Matrix.conjTranspose hcomm
    simpa only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, hstar] using! h.symm
  have hkey : (f.round j)ᴴ * (1 - f.stopAt j) = (1 - f.stopAt j) * (f.round j)ᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, hcomm', Matrix.sub_mul, Matrix.one_mul]
  simp only [CoherentVtFrame.stageOp, coherentStage, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hcompl, hkey, hstar]

/-- The conjugate transpose of a stage operator multiplied by that operator equals the identity. -/
theorem stageOp_adjoint_mul_stageOp (f : CoherentVtFrame H m) (j : Fin m) :
    (f.stageOp j)ᴴ * f.stageOp j = 1 := by
  have hstage := coherentStage_unitary (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
    (f.round_unitary j) (f.round_comm j)
  have h := Matrix.mem_unitaryGroup_iff'.mp hstage
  simpa only [Matrix.star_eq_conjTranspose, CoherentVtFrame.stageOp] using! h

/-- A stage operator multiplied by its conjugate transpose equals the identity. -/
theorem stageOp_mul_stageOp_adjoint (f : CoherentVtFrame H m) (j : Fin m) :
    f.stageOp j * (f.stageOp j)ᴴ = 1 :=
  mul_eq_one_comm.mp (f.stageOp_adjoint_mul_stageOp j)

/-- The single-gate circuit whose gate is the conjugate transpose of the stage operator. -/
def stageInverseCircuit (f : CoherentVtFrame H m) (j : Fin m) : Circuit H :=
  [Step.gate ((f.stageOp j)ᴴ)]

/-- The total matrix of the singleton adjoint-stage list equals the adjoint stage operator. -/
theorem stageInverseCircuit_matrix (f : CoherentVtFrame H m) (j : Fin m) :
    listTotalOp [(f.stageOp j)ᴴ] = (f.stageOp j)ᴴ := by
  simp only [listTotalOp, List.foldr_cons, List.foldr_nil, Matrix.one_mul]

/-- Applying the adjoint stage operator and then the stage operator restores every input state. -/
theorem stageInverseCircuit_inverts (f : CoherentVtFrame H m) (j : Fin m)
    (ψ : QState H) :
    ApplyGate (f.stageOp j) (ApplyGate ((f.stageOp j)ᴴ) ψ) = ψ := by
  rw [← applyGate_mul, f.stageOp_mul_stageOp_adjoint, applyGate_one]

/-- Applying the stage operator and then its adjoint restores every input state. -/
theorem stageInverseCircuit_inverts' (f : CoherentVtFrame H m) (j : Fin m)
    (ψ : QState H) :
    ApplyGate ((f.stageOp j)ᴴ) (ApplyGate (f.stageOp j) ψ) = ψ := by
  rw [← applyGate_mul, f.stageOp_adjoint_mul_stageOp, applyGate_one]

/-- The real-valued reflection price `flagReflectionPrice r` for the supplied parameter `r`. -/
def flagReflectionCost (r : ℕ) : ℝ := flagReflectionPrice r

/-- The sum of the scheduled stage flag-reflection counts over all stages. -/
def flagReflectionCount (rounds : Fin m → ℕ) : ℕ :=
  ∑ j : Fin m, stageFlagCount (rounds j)

/-- The total scheduled flag-reflection count multiplied by the price of one flag reflection. -/
def chargedFlagCost (rounds : Fin m → ℕ) : ℝ :=
  (flagReflectionCount rounds : ℝ) * flagReflectionCost 1

/-- The sum of charged stage-access time and charged flag-reflection cost. -/
def chargedTotalCost (rounds : Fin m → ℕ) : ℝ :=
  chargedAccessTime rounds + chargedFlagCost rounds

/-- The charged flag-reflection cost of every schedule is nonnegative. -/
theorem chargedFlagCost_nonneg (rounds : Fin m → ℕ) :
    0 ≤ chargedFlagCost rounds := by
  unfold chargedFlagCost
  have hcount : 0 ≤ (flagReflectionCount rounds : ℝ) := by
    unfold flagReflectionCount
    have h : (0 : ℕ) ≤ ∑ j : Fin m, stageFlagCount (rounds j) :=
      Finset.sum_nonneg fun j _ => Nat.zero_le _
    exact_mod_cast h
  have hprice : 0 ≤ flagReflectionCost 1 := by
    unfold flagReflectionCost
    simp [flagReflectionPrice]
  positivity

/-- For a positive number of stages, every schedule has positive charged flag-reflection cost. -/
theorem chargedFlagCost_pos (hm : 0 < m) (rounds : Fin m → ℕ) :
    0 < chargedFlagCost rounds := by
  have h1 : ∀ j : Fin m, 0 < (stageFlagCount (rounds j) : ℝ) := by
    intro j
    have h : (0 : ℕ) < stageFlagCount (rounds j) := by
      unfold stageFlagCount stageVisits roundFlagCount
      omega
    exact_mod_cast h
  have hcount : 0 < (flagReflectionCount rounds : ℝ) := by
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have h : 0 < ∑ i : Fin m, (stageFlagCount (rounds i) : ℝ) :=
      Finset.sum_pos (fun i _ => h1 i) Finset.univ_nonempty
    unfold flagReflectionCount
    rw [Nat.cast_sum]
    exact h
  unfold chargedFlagCost
  have hprice : 0 < flagReflectionCost 1 := by
    unfold flagReflectionCost
    simp [flagReflectionPrice]
  positivity

/-- Charged flag cost equals the sum of the paid stage words' known-gate counts multiplied by
the unit flag-reflection price. -/
theorem chargedFlagCost_eq_measured (f : CoherentVtFrame H m) (rounds : Fin m → ℕ) :
    chargedFlagCost rounds
      = ∑ j : Fin m, (Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j (2 * rounds j + 1)) : ℝ)
          * flagReflectionCost 1 := by
  unfold chargedFlagCost flagReflectionCount
  rw [Nat.cast_sum]
  have hleft : (∑ j : Fin m, (stageFlagCount (rounds j) : ℝ)) * flagReflectionCost 1
      = ∑ j : Fin m, (stageFlagCount (rounds j) : ℝ) * flagReflectionCost 1 := by
    rw [Finset.sum_mul]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro j _
  rw [f.stagePaidWord_gateCount j (2 * rounds j + 1)]
  unfold stageFlagCount stageVisits roundFlagCount
  simp only [Nat.cast_mul]
  ring

/-- Charged total cost equals charged access time plus charged flag cost. -/
theorem chargedTotalCost_eq (rounds : Fin m → ℕ) :
    chargedTotalCost rounds = chargedAccessTime rounds + chargedFlagCost rounds := rfl

/-- Charged total cost is at least charged access time. -/
theorem chargedTotalCost_ge_access (rounds : Fin m → ℕ) :
    chargedAccessTime rounds ≤ chargedTotalCost rounds := by
  have h := chargedFlagCost_nonneg rounds
  unfold chargedTotalCost
  linarith

/-- Collects stage-adjoint formulas and inverse identities, odd forward and inverse call counts,
and positive reflection charges with total-cost accounting for a constant schedule. -/
theorem clause2_endpoint_adjointCharge (f : CoherentVtFrame H m) (j : Fin m)
    (hm : 0 < m) (k : ℕ) :

    (f.stageOp j)ᴴ = f.stopAt j + (1 - f.stopAt j) * (f.round j)ᴴ ∧
    (f.stageOp j)ᴴ * f.stageOp j = 1 ∧
    f.stageOp j * (f.stageOp j)ᴴ = 1 ∧

    listTotalOp [(f.stageOp j)ᴴ] = (f.stageOp j)ᴴ ∧
    (∀ ψ : QState H, ApplyGate (f.stageOp j) (ApplyGate ((f.stageOp j)ᴴ) ψ) = ψ) ∧
    (∀ ψ : QState H, ApplyGate ((f.stageOp j)ᴴ) (ApplyGate (f.stageOp j) ψ) = ψ) ∧

    f.stageWordInverseMatrix j = (f.round j)ᴴ ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWord j (2 * k + 1)) j.val = 2 * k + 1 ∧
    Qatlib.Concepts.QlsReadoutSpec.Amplification.calls (f.stagePaidWordInverse j (2 * k + 1)) j.val = 2 * k + 1 ∧

    0 < chargedFlagCost (fun _ : Fin m => k) ∧
    0 ≤ chargedFlagCost (fun _ : Fin m => k) ∧
    chargedTotalCost (fun _ : Fin m => k) = chargedAccessTime (fun _ : Fin m => k) + chargedFlagCost (fun _ : Fin m => k) ∧
    chargedAccessTime (fun _ : Fin m => k) ≤ chargedTotalCost (fun _ : Fin m => k) ∧
    chargedFlagCost (fun _ : Fin m => k)
      = ∑ j' : Fin m, (Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount (f.stagePaidWord j' (2 * k + 1)) : ℝ)
          * flagReflectionCost 1 := by
  refine ⟨f.stageOp_adjoint j, f.stageOp_adjoint_mul_stageOp j,
    f.stageOp_mul_stageOp_adjoint j, f.stageInverseCircuit_matrix j, ?_, ?_,
    f.stageWordInverseMatrix_eq j, f.stagePaidWord_calls_amp j k,
    ?_, ?_, chargedFlagCost_nonneg (fun _ : Fin m => k),
    chargedTotalCost_eq (fun _ : Fin m => k), chargedTotalCost_ge_access (fun _ : Fin m => k),
    chargedFlagCost_eq_measured f (fun _ : Fin m => k)⟩
  · intro ψ
    exact f.stageInverseCircuit_inverts j ψ
  · intro ψ
    exact f.stageInverseCircuit_inverts' j ψ
  · rw [f.stagePaidWordInverse_calls j (2 * k + 1), f.stagePaidWord_calls_amp j k]
  · exact chargedFlagCost_pos hm (fun _ : Fin m => k)

end CoherentVtFrame

namespace CoherentVtFrame

variable {m : ℕ}

/-- The dyadic stopping time at a stage multiplied by that stage's scheduled odd amplification
factor. -/
def amplifiedStopTime (rounds : Fin m → ℕ) (j : Fin m) : ℝ :=
  (2 * rounds j + 1 : ℝ) * stopTime j.val

/-- The sum of the frame's fresh stopping masses times the squared schedule-amplified stopping
times. -/
def amplifiedSecondMomentOf (f : CoherentVtFrame H m) (ψ : QState H)
    (rounds : Fin m → ℕ) : ℝ :=
  ∑ j : Fin m, f.freshStopMass ψ j * (amplifiedStopTime rounds j) ^ 2

/-- The real-valued odd stage multiplier `2 * rounds j + 1` of a schedule. -/
def oddMultiplier (rounds : Fin m → ℕ) (j : Fin m) : ℝ := 2 * rounds j + 1

/-- For normalized input, positive `p`, and `m > 0`, stage windows `(2 * rounds j + 1)² * p ≤ 1
/ m` bound the amplified second moment by `maxStopTime m * averageStopTime m (fun j =>
f.freshStopMass ψ j) / (m * p)`. -/
theorem amplifiedSecondMoment_le_bound (f : CoherentVtFrame H m) (ψ : QState H)
    (hnorm : Normalized ψ) (rounds : Fin m → ℕ) (p : ℝ) (hp : 0 < p) (hm : 0 < m)
    (hwin : ∀ j : Fin m, (2 * rounds j + 1 : ℝ) ^ 2 * p ≤ 1 / (m : ℝ)) :
    amplifiedSecondMomentOf f ψ rounds
      ≤ maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j) / (m * p) := by
  have hq : ∀ j : Fin m, 0 ≤ f.freshStopMass ψ j := fun j => f.freshStopMass_nonneg ψ j
  have hsum : (∑ j : Fin m, f.freshStopMass ψ j) ≤ 1 := by
    have h := f.freshStopMass_total_le ψ
    have h2 : MeasureProb ψ Finset.univ = 1 := measureProb_univ hnorm
    linarith
  have hmul : ∀ j : Fin m, (2 * rounds j + 1 : ℝ) ^ 2 ≤ 1 / (m * p) := by
    intro j
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
    have h2 : (2 * rounds j + 1 : ℝ) ^ 2 * p * (m : ℝ) ≤ 1 := by
      have h := hwin j
      have h3 := (le_div_iff₀ hm0).mp h
      nlinarith [h3]
    have hmp : 0 < m * p := by positivity
    rw [le_div_iff₀ hmp]
    nlinarith [h2]
  have hstep : ∀ j : Fin m,
      f.freshStopMass ψ j * (amplifiedStopTime rounds j) ^ 2
        ≤ f.freshStopMass ψ j * (1 / (m * p)) * (stopTime j.val) ^ 2 := by
    intro j
    have hj := hmul j
    have hq0 := hq j
    rw [amplifiedStopTime]
    calc f.freshStopMass ψ j * ((2 * rounds j + 1 : ℝ) * stopTime j.val) ^ 2
        = f.freshStopMass ψ j * ((2 * rounds j + 1 : ℝ) ^ 2 * (stopTime j.val) ^ 2) := by
          ring
      _ ≤ f.freshStopMass ψ j * ((1 / (m * p)) * (stopTime j.val) ^ 2) := by
          have h := mul_le_mul_of_nonneg_right hj (sq_nonneg (stopTime j.val))
          nlinarith [h, hq0]
      _ = f.freshStopMass ψ j * (1 / (m * p)) * (stopTime j.val) ^ 2 := by ring
  have hmain : amplifiedSecondMomentOf f ψ rounds
      ≤ (1 / (m * p)) * stopSecondMoment m (fun j => f.freshStopMass ψ j) := by
    calc amplifiedSecondMomentOf f ψ rounds
        = ∑ j : Fin m, f.freshStopMass ψ j * (amplifiedStopTime rounds j) ^ 2 := rfl
      _ ≤ ∑ j : Fin m, f.freshStopMass ψ j * (1 / (m * p)) * (stopTime j.val) ^ 2 := by
          exact Finset.sum_le_sum fun j _ => hstep j
      _ = (1 / (m * p)) * stopSecondMoment m (fun j => f.freshStopMass ψ j) := by
          unfold stopSecondMoment
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hbase := stopSecondMoment_le_max_mul_average (fun j => f.freshStopMass ψ j) hq hsum
  calc amplifiedSecondMomentOf f ψ rounds
      ≤ (1 / (m * p)) * stopSecondMoment m (fun j => f.freshStopMass ψ j) := hmain
    _ ≤ (1 / (m * p))
        * (maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j)) := by
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j) / (m * p) := by
        ring

/-- For normalized input and positive `m` and `p`, windows using a relatively accurate estimate
`qhat` bound the amplified second moment by `(1 + c)` times the corresponding
maximum-time/average-time bound divided by `m * p`. -/
theorem amplifiedSecondMoment_le_adaptive (f : CoherentVtFrame H m) (ψ : QState H)
    (hnorm : Normalized ψ) (rounds : Fin m → ℕ) (p : ℝ) (hp : 0 < p) (hm : 0 < m)
    (c qhat : ℝ) (hacc : estimateAccurate c p qhat)
    (hwin : ∀ j : Fin m, (2 * rounds j + 1 : ℝ) ^ 2 * qhat ≤ 1 / (m : ℝ)) :
    amplifiedSecondMomentOf f ψ rounds
      ≤ (1 + c) * (maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j))
          / (m * p) := by
  have hq : ∀ j : Fin m, 0 ≤ f.freshStopMass ψ j := fun j => f.freshStopMass_nonneg ψ j
  have hsum : (∑ j : Fin m, f.freshStopMass ψ j) ≤ 1 := by
    have h := f.freshStopMass_total_le ψ
    have h2 : MeasureProb ψ Finset.univ = 1 := measureProb_univ hnorm
    linarith

  have hacc' : 0 < p → |p - qhat| < c * qhat := hacc.2.1
  have hqh : 0 ≤ qhat := hacc.1
  have hc : 0 ≤ c := by
    have h1 := hacc' hp
    have h2 : 0 < c * qhat := by
      have : 0 ≤ |p - qhat| := abs_nonneg _
      linarith
    by_contra hcon
    have hcon' : c < 0 := lt_of_not_ge hcon
    rcases eq_or_lt_of_le hqh with rfl | hlt
    · linarith
    · have hcq : c * qhat < 0 := by nlinarith
      linarith
  have hlower : p < (1 + c) * qhat := by
    have h1 := hacc' hp
    have h2 : p < qhat + c * qhat := by
      have := abs_lt.mp h1
      linarith [this.1]
    linarith
  have hqhat : 0 < qhat := by
    rcases eq_or_lt_of_le hqh with rfl | hlt
    · linarith
    · exact hlt
  have hmul : ∀ j : Fin m, (2 * rounds j + 1 : ℝ) ^ 2 ≤ (1 + c) / (m * p) := by
    intro j
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
    have h2 : (2 * rounds j + 1 : ℝ) ^ 2 * qhat * (m : ℝ) ≤ 1 := by
      have h := hwin j
      have h3 := (le_div_iff₀ hm0).mp h
      nlinarith [h3]
    have hmp : 0 < m * p := by positivity
    have hbound : (2 * rounds j + 1 : ℝ) ^ 2 * qhat * (m : ℝ) ≤ 1 := h2
    have hqinv : qhat ≤ (1 + c) * qhat := by
      have : 0 ≤ c := hc
      nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt hqhat)]
    rw [le_div_iff₀ hmp]

    have h3 : (2 * rounds j + 1 : ℝ) ^ 2 * (m * p) ≤ (1 + c) := by
      nlinarith [hbound, hlower, hqinv]
    nlinarith
  have hstep : ∀ j : Fin m,
      f.freshStopMass ψ j * (amplifiedStopTime rounds j) ^ 2
        ≤ f.freshStopMass ψ j * ((1 + c) / (m * p)) * (stopTime j.val) ^ 2 := by
    intro j
    have hj := hmul j
    have hq0 := hq j
    rw [amplifiedStopTime]
    calc f.freshStopMass ψ j * ((2 * rounds j + 1 : ℝ) * stopTime j.val) ^ 2
        = f.freshStopMass ψ j * ((2 * rounds j + 1 : ℝ) ^ 2 * (stopTime j.val) ^ 2) := by
          ring
      _ ≤ f.freshStopMass ψ j * (((1 + c) / (m * p)) * (stopTime j.val) ^ 2) := by
          have h := mul_le_mul_of_nonneg_right hj (sq_nonneg (stopTime j.val))
          nlinarith [h, hq0]
      _ = f.freshStopMass ψ j * ((1 + c) / (m * p)) * (stopTime j.val) ^ 2 := by ring
  have hmain : amplifiedSecondMomentOf f ψ rounds
      ≤ ((1 + c) / (m * p)) * stopSecondMoment m (fun j => f.freshStopMass ψ j) := by
    calc amplifiedSecondMomentOf f ψ rounds
        = ∑ j : Fin m, f.freshStopMass ψ j * (amplifiedStopTime rounds j) ^ 2 := rfl
      _ ≤ ∑ j : Fin m, f.freshStopMass ψ j * ((1 + c) / (m * p)) * (stopTime j.val) ^ 2 := by
          exact Finset.sum_le_sum fun j _ => hstep j
      _ = ((1 + c) / (m * p))
          * stopSecondMoment m (fun j => f.freshStopMass ψ j) := by
          unfold stopSecondMoment
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hbase := stopSecondMoment_le_max_mul_average (fun j => f.freshStopMass ψ j) hq hsum
  calc amplifiedSecondMomentOf f ψ rounds
      ≤ ((1 + c) / (m * p)) * stopSecondMoment m (fun j => f.freshStopMass ψ j) := hmain
    _ ≤ ((1 + c) / (m * p))
        * (maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j)) := by
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (1 + c) * (maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j))
          / (m * p) := by ring

/-- For normalized input, positive `m` and `p`, and positive measurements at least `p`, policy
stage windows yield the amplified second-moment bound with denominator `m * p`. -/
theorem amplifiedSecondMoment_le_policy (f : CoherentVtFrame H m) (ψ : QState H)
    (hnorm : Normalized ψ) (pol : StagePolicy) (measured : Fin m → ℝ)
    (hpos : ∀ j, 0 < measured j) (p : ℝ) (hp : 0 < p) (hm : 0 < m)
    (hpmeas : ∀ j : Fin m, p ≤ measured j)
    (hwin : ∀ j : Fin m,
      (2 * policySchedule pol measured j + 1 : ℝ) ^ 2 * measured j ≤ 1 / (m : ℝ)) :
    amplifiedSecondMomentOf f ψ (policySchedule pol measured)
      ≤ maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j) / (m * p) := by
  refine amplifiedSecondMoment_le_bound f ψ hnorm (policySchedule pol measured) p hp hm ?_
  intro j
  have h1 := hwin j
  have h2 := hpmeas j
  have h3 : 0 < measured j := hpos j
  have h4 : (2 * policySchedule pol measured j + 1 : ℝ) ^ 2 * p
      ≤ (2 * policySchedule pol measured j + 1 : ℝ) ^ 2 * measured j := by
    have : 0 ≤ (2 * policySchedule pol measured j + 1 : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt h3)]
  linarith

/-- For normalized input and the stated stage windows, collects the amplified stopping-time
formula, its second-moment expansion and upper bound, and the conditional reciprocal-success
lower bound on squared multipliers. -/
theorem clause3_endpoint_amplified (f : CoherentVtFrame H m) (ψ : QState H)
    (hnorm : Normalized ψ) (rounds : Fin m → ℕ) (p : ℝ) (hp : 0 < p) (hm : 0 < m)
    (hwin : ∀ j : Fin m, (2 * rounds j + 1 : ℝ) ^ 2 * p ≤ 1 / (m : ℝ)) :

    (∀ j : Fin m, amplifiedStopTime rounds j = (2 * rounds j + 1 : ℝ) * stopTime j.val) ∧
    amplifiedSecondMomentOf f ψ rounds
      = ∑ j : Fin m, f.freshStopMass ψ j
          * ((2 * rounds j + 1 : ℝ) * stopTime j.val) ^ 2 ∧

    amplifiedSecondMomentOf f ψ rounds
      ≤ maxStopTime m * averageStopTime m (fun j => f.freshStopMass ψ j) / (m * p) ∧

    (∀ j : Fin m, (2 * rounds j + 1 : ℝ) ^ 2 * p ≥ 1 →
        (2 * rounds j + 1 : ℝ) ^ 2 ≥ 1 / p) := by
  refine ⟨fun j => rfl, rfl, amplifiedSecondMoment_le_bound f ψ hnorm rounds p hp hm hwin, ?_⟩
  intro j hj
  have hp0 : 0 < p := hp
  have hA : (1 / p) ≤ (2 * rounds j + 1 : ℝ) ^ 2 := by
    rw [div_le_iff₀ hp0]
    exact hj
  exact hA

end CoherentVtFrame

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
