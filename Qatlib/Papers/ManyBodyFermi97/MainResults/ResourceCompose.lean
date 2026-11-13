/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.ExchangeSign
import Qatlib.Papers.ManyBodyFermi97.MainResults.Measurement

/-!
# Composition of first-quantized resource counts

This module combines antisymmetrization and per-particle step costs into
`firstQuantHubbardTotalCost`. `totalSchedule` realizes that count by appending identity gates to
the exchange-sign schedule; the results establish gate counts, unitarity, and query counts for
this accounting circuit and its repetitions.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `firstQuantHubbardTotalCost_bound`: For positive `n` and `q`, the total resource count is at
  most `18 * n ^ 2 * q ^ 2`.
* `totalSchedule_gateCount`: The gate count of the accounting schedule equals
  `firstQuantHubbardTotalCost n q`.
* `repeatedSchedule_bound`: For positive `n` and `q`, the repeated accounting schedule has at
  most `18 * T * n ^ 2 * q ^ 2` gates.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.ResourceCompose
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Classical BigOperators

/-- The sum of the first-quantized Hubbard step costs for `n` particles, each using word size
`q`. -/
def perParticleStepCost (n q : ℕ) : ℕ := n * firstQuantHubbardStepCost q

/-- The antisymmetrization cost plus the per-particle Hubbard step cost. -/
def firstQuantHubbardTotalCost (n q : ℕ) : ℕ :=
  antisymTotalCost n q + perParticleStepCost n q

/-- For positive `n` and `q`, the combined per-particle cost is at most `14 * n ^ 2 * q ^ 2`. -/
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

/-- For positive `n` and `q`, the total resource count is at most `18 * n ^ 2 * q ^ 2`.
[AbramsLloyd1997] -/
theorem firstQuantHubbardTotalCost_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    firstQuantHubbardTotalCost n q ≤ 18 * n ^ 2 * q ^ 2 := by
  unfold firstQuantHubbardTotalCost
  have ha := antisymTotalCost_bound hn hq
  have hb := perParticleStepCost_bound hn hq
  calc antisymTotalCost n q + perParticleStepCost n q
      ≤ 4 * n ^ 2 * q ^ 2 + 14 * n ^ 2 * q ^ 2 := Nat.add_le_add ha hb
    _ = 18 * n ^ 2 * q ^ 2 := by ring

/-- Expands the total cost as the antisymmetrization cost plus `n` times the single-particle
step cost. [AbramsLloyd1997] -/
theorem firstQuantHubbardTotalCost_eq (n q : ℕ) :
    firstQuantHubbardTotalCost n q =
      antisymTotalCost n q + n * firstQuantHubbardStepCost q := rfl

/-- The exchange-sign accounting schedule followed by `perParticleStepCost n q` identity gates. -/
def totalSchedule (I : Type*) [Fintype I] [DecidableEq I] (n q : ℕ) : Circuit I :=
  ExchangeSign.schedule I n q ++
    List.replicate (perParticleStepCost n q) (Step.gate (1 : Matrix I I ℂ))

/-- A list consisting entirely of identity gates has query count zero. -/
theorem queryCount_replicate_gate {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) :
    QueryCount (List.replicate k (Step.gate (1 : Matrix I I ℂ))) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The gate count of the accounting schedule equals `firstQuantHubbardTotalCost n q`.
[AbramsLloyd1997] -/
theorem totalSchedule_gateCount {I : Type*} [Fintype I] [DecidableEq I]
    (n q : ℕ) :
    GateCount (totalSchedule I n q) = firstQuantHubbardTotalCost n q := by
  unfold totalSchedule firstQuantHubbardTotalCost perParticleStepCost
  rw [gateCount_append, ExchangeSign.schedule_gateCount]
  congr 1
  induction n * firstQuantHubbardStepCost q with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The accounting schedule is unitary and has query count zero. [AbramsLloyd1997] -/
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

/-- Repeats the total accounting schedule `T` times. -/
def repeatedSchedule (I : Type*) [Fintype I] [DecidableEq I]
    (n q T : ℕ) : Circuit I :=
  RepeatCircuit (totalSchedule I n q) T

/-- Repeating the accounting schedule `T` times multiplies its gate count by `T`.
[AbramsLloyd1997] -/
theorem repeatedSchedule_gateCount {I : Type*} [Fintype I] [DecidableEq I]
    (n q T : ℕ) :
    GateCount (repeatedSchedule I n q T) = T * firstQuantHubbardTotalCost n q := by
  unfold repeatedSchedule
  rw [gateCount_repeatCircuit, totalSchedule_gateCount]

/-- For positive `n` and `q`, the repeated accounting schedule has at most `18 * T * n ^ 2 * q ^
2` gates. [AbramsLloyd1997] -/
theorem repeatedSchedule_bound {I : Type*} [Fintype I] [DecidableEq I]
    {n q T : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    GateCount (repeatedSchedule I n q T) ≤ 18 * T * n ^ 2 * q ^ 2 := by
  rw [repeatedSchedule_gateCount]
  have h := firstQuantHubbardTotalCost_bound hn hq
  calc T * firstQuantHubbardTotalCost n q ≤ T * (18 * n ^ 2 * q ^ 2) :=
        Nat.mul_le_mul_left T h
    _ = 18 * T * n ^ 2 * q ^ 2 := by ring

/-- Every finite repetition of the accounting schedule is unitary and has query count zero.
[AbramsLloyd1997] -/
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
