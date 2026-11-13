/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSystemSim96.MainResults.QftKernelBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Gate costs for repeated finite-grid simulation

This module records exact local QFT and sandwich-circuit gate counts, together with abstract
resource comparisons motivated by [Zalka1998]. `simulationStep` places the local QFT between
supplied circuits, while `quantumSimulationCost` and `classicalSimulationCost` define the total
cost models for repeated steps and multiple registers.

The comparison theorems retain explicit hypotheses bounding each diagonal cost by
`classicalStepCost`. `quantumDiagonalCost` separately accounts for a computation, its reversal,
and one phase per value bit.

## Main statements

* `simulationStep_gateCount` and `repeatedSimulationStep_gateCount` give exact circuit gate
  counts.
* `qftGateCost_le_sq_add` and `qftGateCost_le_classicalStepCost` compare the QFT count with
  quadratic and FFT-style expressions.
* `quantumDiagonalCost_le_two_classical` bounds the compute-phase-uncompute cost model.
* `quantumSimulationCost_le_classical` gives a factor-three comparison under the stated
  diagonal-cost bounds.

## References

* [Zalka, 1998][Zalka1998]
-/

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

/-- The exact local QFT gate-count expression `n + n * (n - 1) / 2 + n / 2`. -/
def qftGateCost (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

/-- The local QFT gate count is at most `n * n + n`. -/
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

/-- The FFT-style comparison cost `2 ^ n * n` for an `n`-bit grid register. -/
def classicalStepCost (n : ℕ) : ℕ := 2 ^ n * n

/-- The exact local QFT gate count is bounded by the comparison expression `2 ^ n * n`,
supporting the cost comparison in [Zalka1998]. -/
theorem qftGateCost_le_classicalStepCost (n : ℕ) :
    qftGateCost n ≤ classicalStepCost n := by
  have hq := qftGateCost_le_sq_add n
  have hp : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
  unfold classicalStepCost
  calc qftGateCost n ≤ n * n + n := hq
    _ = n * (n + 1) := by ring
    _ ≤ n * 2 ^ n := Nat.mul_le_mul_left n hp
    _ = 2 ^ n * n := by ring

/-- The circuit formed by a supplied pre-circuit, the actual local QFT circuit, and a supplied
post-circuit, in that execution order. -/
def simulationStep (n : ℕ) (Cpre Cpost : Circuit (Reg n)) : Circuit (Reg n) :=
  Cpre ++ localProgramCircuit (localQFT n) ++ Cpost

/-- The simulation sandwich has gate count equal to the two endpoint counts plus `qftGateCost
n`, giving exact step accounting for [Zalka1998]. -/
theorem simulationStep_gateCount (n : ℕ) (Cpre Cpost : Circuit (Reg n)) :
    GateCount (simulationStep n Cpre Cpost) =
      GateCount Cpre + qftGateCost n + GateCount Cpost := by
  simpa [simulationStep, qftGateCost] using
    (diagonalQftSandwichCosts n Cpre Cpost).1

/-- Repeating the same simulation sandwich `T` times multiplies its exact gate count by `T`, as
used in the simulation cost accounting of [Zalka1998]. -/
theorem repeatedSimulationStep_gateCount (T n : ℕ) (Cpre Cpost : Circuit (Reg n)) :
    GateCount (RepeatCircuit (simulationStep n Cpre Cpost) T) =
      T * (GateCount Cpre + qftGateCost n + GateCount Cpost) := by
  rw [gateCount_repeatCircuit, simulationStep_gateCount]

/-- The register-size expression `d * n` for `d` coordinate registers of `n` qubits each. -/
def totalQubits (d n : ℕ) : ℕ := d * n

/-- Three coordinate registers of `n` qubits give the register-size expression `3 * n`, as in
the spatial encoding of [Zalka1998]. -/
theorem totalQubits_three_dims (n : ℕ) : totalQubits 3 n = 3 * n := rfl

/-- The sum of `d` identical local QFT gate costs, expressed as `d * qftGateCost n`. -/
def multiQftGateCost (d n : ℕ) : ℕ := d * qftGateCost n

/-- The cost of `d` local QFTs is at most `d * (n * n + n)`. -/
theorem multiQftGateCost_le (d n : ℕ) :
    multiQftGateCost d n ≤ d * (n * n + n) := by
  unfold multiQftGateCost
  exact Nat.mul_le_mul_left d (qftGateCost_le_sq_add n)

/-- The cost of `d` local QFTs is bounded by `d * classicalStepCost n`, giving the multiregister
comparison used for [Zalka1998]. -/
theorem multiQftGateCost_le_classical (d n : ℕ) :
    multiQftGateCost d n ≤ d * classicalStepCost n := by
  unfold multiQftGateCost
  exact Nat.mul_le_mul_left d (qftGateCost_le_classicalStepCost n)

/-- The cost-model expression `2 * C + r` for computation, its reversal, and `r` value-bit phase
gates. -/
def quantumDiagonalCost (C r : ℕ) : ℕ := 2 * C + r

/-- The comparison cost-model expression `C + r` for a computation cost `C` and a value-register
size `r`. -/
def classicalDiagonalCost (C r : ℕ) : ℕ := C + r

/-- The compute-phase-uncompute cost model `2 * C + r` is at most twice `C + r`, providing a
diagonal-cost comparison for [Zalka1998]. -/
theorem quantumDiagonalCost_le_two_classical (C r : ℕ) :
    quantumDiagonalCost C r ≤ 2 * classicalDiagonalCost C r := by
  unfold quantumDiagonalCost classicalDiagonalCost
  omega

/-- The total model cost `T * d * (cpre + qftGateCost n + cpost)` for `T` steps on `d`
registers. -/
def quantumSimulationCost (T d n cpre cpost : ℕ) : ℕ :=
  T * d * (cpre + qftGateCost n + cpost)

/-- The total comparison cost `T * d * classicalStepCost n`. -/
def classicalSimulationCost (T d n : ℕ) : ℕ := T * d * classicalStepCost n

/-- If each diagonal cost is at most `classicalStepCost n`, the total quantum cost model is at
most three times the classical comparison model, making the cost assumptions in the
comparison with [Zalka1998] explicit. -/
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

/-- If both endpoint costs are bounded by `classicalStepCost n`, their sum with the local QFT
cost is at most three times that benchmark. -/
theorem stepCost_le_three_classical {n cpre cpost : ℕ}
    (hpre : cpre ≤ classicalStepCost n) (hpost : cpost ≤ classicalStepCost n) :
    cpre + qftGateCost n + cpost ≤ 3 * classicalStepCost n := by
  have hq := qftGateCost_le_classicalStepCost n
  omega

end Qatlib.Papers.QSystemSim96.MainResults
