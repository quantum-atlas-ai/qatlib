/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.ExchangeSign
import Qatlib.Papers.ManyBodyFermi97.MainResults.Measurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.ResourceCompose
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Classical BigOperators

def perParticleStepCost (n q : ℕ) : ℕ := n * firstQuantHubbardStepCost q

def firstQuantHubbardTotalCost (n q : ℕ) : ℕ :=
  antisymTotalCost n q + perParticleStepCost n q

theorem perParticleStepCost_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    perParticleStepCost n q ≤ 14 * n ^ 2 * q ^ 2 := by
  unfold perParticleStepCost
  have hstep := firstQuantHubbardStepCost_bound hq
  have hmul : n * firstQuantHubbardStepCost q ≤ n * (14 * q ^ 2) :=
    Nat.mul_le_mul_left n hstep
  have hn2 : n ≤ n ^ 2 := sq_ge_self hn
  calc n * firstQuantHubbardStepCost q ≤ n * (14 * q ^ 2) := hmul
    _ = 14 * n * q ^ 2 := by ring
    _ = 14 * (n * q ^ 2) := by ring
    _ ≤ 14 * (n ^ 2 * q ^ 2) := Nat.mul_le_mul_left 14 (Nat.mul_le_mul_right _ hn2)
    _ = 14 * n ^ 2 * q ^ 2 := by ring

theorem firstQuantHubbardTotalCost_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    firstQuantHubbardTotalCost n q ≤ 18 * n ^ 2 * q ^ 2 := by
  unfold firstQuantHubbardTotalCost
  have ha := antisymTotalCost_bound hn hq
  have hb := perParticleStepCost_bound hn hq
  calc antisymTotalCost n q + perParticleStepCost n q
      ≤ 4 * n ^ 2 * q ^ 2 + 14 * n ^ 2 * q ^ 2 := Nat.add_le_add ha hb
    _ = 18 * n ^ 2 * q ^ 2 := by ring

theorem firstQuantHubbardTotalCost_eq (n q : ℕ) :
    firstQuantHubbardTotalCost n q =
      antisymTotalCost n q + n * firstQuantHubbardStepCost q := rfl

def totalSchedule (I : Type*) [Fintype I] [DecidableEq I] (n q : ℕ) : Circuit I :=
  ExchangeSign.schedule I n q ++
    List.replicate (perParticleStepCost n q) (Step.gate (1 : Matrix I I ℂ))

theorem queryCount_replicate_gate {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) :
    QueryCount (List.replicate k (Step.gate (1 : Matrix I I ℂ))) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem totalSchedule_gateCount {I : Type*} [Fintype I] [DecidableEq I]
    (n q : ℕ) :
    GateCount (totalSchedule I n q) = firstQuantHubbardTotalCost n q := by
  unfold totalSchedule firstQuantHubbardTotalCost perParticleStepCost
  rw [gateCount_append, ExchangeSign.schedule_gateCount]
  congr 1
  induction n * firstQuantHubbardStepCost q with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem totalSchedule_correct {I : Type*} [Fintype I] [DecidableEq I]
    (n q : ℕ) :
    IsUnitaryCircuit (totalSchedule I n q) ∧
      QueryCount (totalSchedule I n q) = 0 := by
  constructor
  · have hrep : IsUnitaryCircuit
        (List.replicate (perParticleStepCost n q) (Step.gate (1 : Matrix I I ℂ))) := by
      induction perParticleStepCost n q with
      | zero => simp
      | succ k ih => simp [List.replicate_succ, ih]
    unfold totalSchedule
    exact (isUnitaryCircuit_append _ _).mpr ⟨(ExchangeSign.schedule_correct n q).1, hrep⟩
  · unfold totalSchedule
    rw [queryCount_append, (ExchangeSign.schedule_correct n q).2,
      queryCount_replicate_gate, Nat.add_zero]

def repeatedSchedule (I : Type*) [Fintype I] [DecidableEq I]
    (n q T : ℕ) : Circuit I :=
  RepeatCircuit (totalSchedule I n q) T

theorem repeatedSchedule_gateCount {I : Type*} [Fintype I] [DecidableEq I]
    (n q T : ℕ) :
    GateCount (repeatedSchedule I n q T) = T * firstQuantHubbardTotalCost n q := by
  unfold repeatedSchedule
  rw [gateCount_repeatCircuit, totalSchedule_gateCount]

theorem repeatedSchedule_bound {I : Type*} [Fintype I] [DecidableEq I]
    {n q T : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    GateCount (repeatedSchedule I n q T) ≤ 18 * T * n ^ 2 * q ^ 2 := by
  rw [repeatedSchedule_gateCount]
  have h := firstQuantHubbardTotalCost_bound hn hq
  calc T * firstQuantHubbardTotalCost n q ≤ T * (18 * n ^ 2 * q ^ 2) :=
        Nat.mul_le_mul_left T h
    _ = 18 * T * n ^ 2 * q ^ 2 := by ring

theorem repeatedSchedule_correct {I : Type*} [Fintype I] [DecidableEq I]
    (n q T : ℕ) :
    IsUnitaryCircuit (repeatedSchedule I n q T) ∧
      QueryCount (repeatedSchedule I n q T) = 0 := by
  constructor
  · unfold repeatedSchedule
    exact IsUnitaryCircuit.repeatCircuit (totalSchedule_correct n q).1 T
  · unfold repeatedSchedule
    rw [queryCount_repeatCircuit, (totalSchedule_correct n q).2, Nat.mul_zero]

end Qatlib.Papers.ManyBodyFermi97.MainResults.ResourceCompose
