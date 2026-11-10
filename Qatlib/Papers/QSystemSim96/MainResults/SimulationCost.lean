/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSystemSim96.MainResults.QftKernelBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Matrix
open scoped BigOperators
noncomputable section
namespace Qatlib.Papers.QSystemSim96.MainResults

def qftGateCost (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

theorem qftGateCost_le_sq_add (n : ℕ) : qftGateCost n ≤ n * n + n := by
  unfold qftGateCost
  have h1 : n * (n - 1) / 2 * 2 ≤ n * (n - 1) := Nat.div_mul_le_self _ 2
  have h2 : n / 2 * 2 ≤ n := Nat.div_mul_le_self _ 2
  have h3 : (n * (n - 1) / 2 + n / 2) * 2 ≤ n * (n - 1) + n := by
    rw [Nat.add_mul]
    omega
  have h4 : n * (n - 1) + n = n * n := by
    cases n with
    | zero => simp
    | succ m => rw [Nat.succ_sub_one]; ring
  have h5 : n * (n - 1) / 2 + n / 2 ≤
      (n * (n - 1) / 2 + n / 2) * 2 := by omega
  omega

def classicalStepCost (n : ℕ) : ℕ := 2 ^ n * n

theorem qftGateCost_le_classicalStepCost (n : ℕ) :
    qftGateCost n ≤ classicalStepCost n := by
  have hq := qftGateCost_le_sq_add n
  have hp : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
  unfold classicalStepCost
  calc qftGateCost n ≤ n * n + n := hq
    _ = n * (n + 1) := by ring
    _ ≤ n * 2 ^ n := Nat.mul_le_mul_left n hp
    _ = 2 ^ n * n := by ring

def simulationStep (n : ℕ) (Cpre Cpost : Circuit (Reg n)) : Circuit (Reg n) :=
  Cpre ++ localProgramCircuit (localQFT n) ++ Cpost

theorem simulationStep_gateCount (n : ℕ) (Cpre Cpost : Circuit (Reg n)) :
    GateCount (simulationStep n Cpre Cpost) =
      GateCount Cpre + qftGateCost n + GateCount Cpost := by
  simpa [simulationStep, qftGateCost] using
    (diagonalQftSandwichCosts n Cpre Cpost).1

theorem repeatedSimulationStep_gateCount (T n : ℕ) (Cpre Cpost : Circuit (Reg n)) :
    GateCount (RepeatCircuit (simulationStep n Cpre Cpost) T) =
      T * (GateCount Cpre + qftGateCost n + GateCount Cpost) := by
  rw [gateCount_repeatCircuit, simulationStep_gateCount]

def totalQubits (d n : ℕ) : ℕ := d * n

theorem totalQubits_three_dims (n : ℕ) : totalQubits 3 n = 3 * n := rfl

def multiQftGateCost (d n : ℕ) : ℕ := d * qftGateCost n

theorem multiQftGateCost_le (d n : ℕ) :
    multiQftGateCost d n ≤ d * (n * n + n) := by
  unfold multiQftGateCost
  exact Nat.mul_le_mul_left d (qftGateCost_le_sq_add n)

theorem multiQftGateCost_le_classical (d n : ℕ) :
    multiQftGateCost d n ≤ d * classicalStepCost n := by
  unfold multiQftGateCost
  exact Nat.mul_le_mul_left d (qftGateCost_le_classicalStepCost n)

def quantumDiagonalCost (C r : ℕ) : ℕ := 2 * C + r

def classicalDiagonalCost (C r : ℕ) : ℕ := C + r

theorem quantumDiagonalCost_le_two_classical (C r : ℕ) :
    quantumDiagonalCost C r ≤ 2 * classicalDiagonalCost C r := by
  unfold quantumDiagonalCost classicalDiagonalCost
  omega

def quantumSimulationCost (T d n cpre cpost : ℕ) : ℕ :=
  T * d * (cpre + qftGateCost n + cpost)

def classicalSimulationCost (T d n : ℕ) : ℕ := T * d * classicalStepCost n

theorem quantumSimulationCost_le_classical {T d n cpre cpost : ℕ}
    (hpre : cpre ≤ classicalStepCost n) (hpost : cpost ≤ classicalStepCost n) :
    quantumSimulationCost T d n cpre cpost ≤ 3 * classicalSimulationCost T d n := by
  unfold quantumSimulationCost classicalSimulationCost
  have hq := qftGateCost_le_classicalStepCost n
  have hsum : cpre + qftGateCost n + cpost ≤ 3 * classicalStepCost n := by
    omega
  calc T * d * (cpre + qftGateCost n + cpost)
      ≤ T * d * (3 * classicalStepCost n) := Nat.mul_le_mul_left (T * d) hsum
    _ = 3 * (T * d * classicalStepCost n) := by ring

theorem stepCost_le_three_classical {n cpre cpost : ℕ}
    (hpre : cpre ≤ classicalStepCost n) (hpost : cpost ≤ classicalStepCost n) :
    cpre + qftGateCost n + cpost ≤ 3 * classicalStepCost n := by
  have hq := qftGateCost_le_classicalStepCost n
  omega

end Qatlib.Papers.QSystemSim96.MainResults
