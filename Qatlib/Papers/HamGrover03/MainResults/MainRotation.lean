/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Search Rotations and Oracle Circuits

This module formalizes exact Grover rotation and the scalar comparison schedules associated with
the Hamiltonian search algorithms of [RolandCerf2003]. `grover_constant_angular_velocity`
advances the marked-vector angle by `2*j*theta`, where `sin(theta)^2` is the marked fraction and
both `sin(theta)` and `cos(theta)` are nonzero. Separately, `groverAngle`, `analogAngle`, and
`adiabaticAngle` encode scalar schedules, with floor-based step counts and terminal-angle
bounds. The analog and adiabatic schedule identities here are arithmetic statements.

`hamStep` composes constant-Hamiltonian evolutions as `exp(-i*t0*H0) * exp(-i*tf*Hf)` and is
unitary for Hermitian inputs. `oracleHamStepCircuit` computes a Boolean predicate into an
ancilla, applies `phaseGate`, and uncomputes it using two oracle queries. On an initially false
ancilla, it multiplies unmarked amplitudes by `exp(-i*t)` and marked amplitudes by `1`,
restoring the ancilla to false.

## Main statements

* `constant_angular_velocity_schedules` gives the fixed increments of the three scalar angle
  schedules.
- `grover_constant_angular_velocity` proves exact rotation on two-amplitude marked vectors.
* `analog_angle_at_stepCount_le` and `adiabatic_angle_at_stepCount_le` bound the scalar terminal
  angles by `pi/2`.
- `hamStep_unitary` proves unitarity of the composed Hamiltonian step.
- `run_oracleHamStepCircuit` evaluates the two-query phase implementation.
* `main_constant_angular_velocity_and_circuit_implementation` collects these rotation, schedule,
  unitarity, and query statements.

## References

- [Roland and Cerf, 2003][RolandCerf2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators
open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.HamGrover03.MainResults

/-- The Boolean-indexed state with amplitude `sin(alpha)` at true and `cos(alpha)` at false. -/
def planeState (α : ℝ) : QState Bool :=
  fun b => if b then (Real.sin α : ℂ) else (Real.cos α : ℂ)

/-- Every `planeState alpha` is normalized, by the identity `sin(alpha)^2 + cos(alpha)^2 = 1`. -/
theorem normalized_planeState (α : ℝ) : Normalized (planeState α) := by
  unfold Normalized planeState
  rw [Fintype.sum_bool]
  simp only [eq_self, Bool.false_eq_true, if_true, if_false, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- The scalar comparison angle `2*j/sqrt(N)` after `j` Grover steps. -/
def groverAngle (N : ℕ) (j : ℕ) : ℝ :=
  2 * (j : ℝ) / Real.sqrt (N : ℝ)

/-- The fixed increment `2/sqrt(N)` of the scalar Grover comparison schedule. -/
def groverIncrement (N : ℕ) : ℝ := 2 / Real.sqrt (N : ℝ)

/-- The scalar analog comparison angle `(pi/2)*epsilon*j/sqrt(N)` at step `j`. -/
def analogAngle (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  (Real.pi / 2) * (ε * (j : ℝ) / Real.sqrt (N : ℝ))

/-- The fixed increment `(pi/2)*epsilon/sqrt(N)` of the scalar analog schedule. -/
def analogIncrement (N : ℕ) (ε : ℝ) : ℝ :=
  (Real.pi / 2) * (ε / Real.sqrt (N : ℝ))

/-- The scalar adiabatic comparison angle `(pi/2)*epsilon^3*j/sqrt(N)` at step `j`. -/
def adiabaticAngle (N : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  (Real.pi / 2) * (ε ^ 3 * (j : ℝ) / Real.sqrt (N : ℝ))

/-- The fixed increment `(pi/2)*epsilon^3/sqrt(N)` of the scalar adiabatic schedule. -/
def adiabaticIncrement (N : ℕ) (ε : ℝ) : ℝ :=
  (Real.pi / 2) * (ε ^ 3 / Real.sqrt (N : ℝ))

/-- The natural-number floor of `(pi/4)*sqrt(N)`, used as the scalar Grover schedule's step
count. -/
def groverStepCount (N : ℕ) : ℕ := ⌊(Real.pi / 4) * Real.sqrt (N : ℝ)⌋₊

/-- The natural-number floor of `sqrt(N)/epsilon`, used as the scalar analog schedule's step
count. -/
def analogStepCount (N : ℕ) (ε : ℝ) : ℕ := ⌊Real.sqrt (N : ℝ) / ε⌋₊

/-- The natural-number floor of `sqrt(N)/epsilon^3`, used as the scalar adiabatic schedule's
step count. -/
def adiabaticStepCount (N : ℕ) (ε : ℝ) : ℕ := ⌊Real.sqrt (N : ℝ) / ε ^ 3⌋₊

/-- The initial-Hamiltonian time allocation `(1-s)*epsilon^2*(pi/2)` in the scalar adiabatic
discretization. -/
def adiabaticDt0 (ε s : ℝ) : ℝ := (1 - s) * ε ^ 2 * (Real.pi / 2)

/-- The final-Hamiltonian time allocation `s*epsilon^2*(pi/2)` in the scalar adiabatic
discretization. -/
def adiabaticDtf (ε s : ℝ) : ℝ := s * ε ^ 2 * (Real.pi / 2)

/-- The two adiabatic time allocations sum to `epsilon^2*(pi/2)` for every real `epsilon` and
`s`. -/
theorem adiabatic_dt_add (ε s : ℝ) :
    adiabaticDt0 ε s + adiabaticDtf ε s = ε ^ 2 * (Real.pi / 2) := by
  unfold adiabaticDt0 adiabaticDtf
  ring

/-- Increasing the Grover schedule's step index by one adds `groverIncrement N` to its scalar
angle. -/
theorem groverAngle_succ (N : ℕ) (j : ℕ) :
    groverAngle N (j + 1) = groverAngle N j + groverIncrement N := by
  unfold groverAngle groverIncrement
  push_cast
  ring

/-- Increasing the analog schedule's step index by one adds `analogIncrement N epsilon` to its
scalar angle. -/
theorem analogAngle_succ (N : ℕ) (ε : ℝ) (j : ℕ) :
    analogAngle N ε (j + 1) = analogAngle N ε j + analogIncrement N ε := by
  unfold analogAngle analogIncrement
  push_cast
  ring

/-- Increasing the adiabatic schedule's step index by one adds `adiabaticIncrement N epsilon` to
its scalar angle. -/
theorem adiabaticAngle_succ (N : ℕ) (ε : ℝ) (j : ℕ) :
    adiabaticAngle N ε (j + 1) = adiabaticAngle N ε j + adiabaticIncrement N ε := by
  unfold adiabaticAngle adiabaticIncrement
  push_cast
  ring

/-- The Grover, analog, and adiabatic scalar schedules each have an increment independent of the
step index, with the respective increments defined in this module [RolandCerf2003]. -/
theorem constant_angular_velocity_schedules (N : ℕ) (ε : ℝ) :
    (∀ j : ℕ, groverAngle N (j + 1) = groverAngle N j + groverIncrement N) ∧
    (∀ j : ℕ, analogAngle N ε (j + 1) = analogAngle N ε j + analogIncrement N ε) ∧
    (∀ j : ℕ, adiabaticAngle N ε (j + 1) = adiabaticAngle N ε j + adiabaticIncrement N ε) :=
  ⟨groverAngle_succ N, analogAngle_succ N ε, adiabaticAngle_succ N ε⟩

/-- For positive `c`, the natural-number floor of `sqrt(N)/c` is at most that ratio, and the
ratio is strictly less than the floor plus one. -/
theorem stepCount_bounds {N : ℕ} {c : ℝ} (hc : 0 < c) :
    ((⌊Real.sqrt (N : ℝ) / c⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / c ∧
      Real.sqrt (N : ℝ) / c < ((⌊Real.sqrt (N : ℝ) / c⌋₊ : ℕ) : ℝ) + 1 :=
  ⟨Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) hc.le), Nat.lt_floor_add_one _⟩

/-- The real value of `groverStepCount N` is at most `(pi/4)*sqrt(N)`, which is strictly less
than that count plus one. -/
theorem grover_stepCount_bounds (N : ℕ) :
    ((groverStepCount N : ℝ) ≤ (Real.pi / 4) * Real.sqrt (N : ℝ)) ∧
      (Real.pi / 4) * Real.sqrt (N : ℝ) < (groverStepCount N : ℝ) + 1 := by
  unfold groverStepCount
  exact ⟨Nat.floor_le (mul_nonneg (by positivity) (Real.sqrt_nonneg _)),
    Nat.lt_floor_add_one _⟩

/-- For positive `N` and `c`, the angle `(pi/2)*c*floor(sqrt(N)/c)/sqrt(N)` is at most `pi/2`,
using the natural-number floor. -/
theorem angle_at_stepCount_le {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : 0 < c) :
    (Real.pi / 2) * (c * ((⌊Real.sqrt (N : ℝ) / c⌋₊ : ℕ) : ℝ) / Real.sqrt (N : ℝ)) ≤
      Real.pi / 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos_of_pos hNpos
  have hq : 0 ≤ Real.sqrt (N : ℝ) / c := div_nonneg hsqrt.le hc.le
  have hle : ((⌊Real.sqrt (N : ℝ) / c⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / c :=
    Nat.floor_le hq
  have hmul : c * ((⌊Real.sqrt (N : ℝ) / c⌋₊ : ℕ) : ℝ) / Real.sqrt (N : ℝ) ≤ 1 := by
    rw [div_le_one hsqrt]
    have hm := mul_le_mul_of_nonneg_left hle hc.le
    rwa [mul_div_cancel₀ (Real.sqrt (N : ℝ)) hc.ne'] at hm
  calc (Real.pi / 2) * (c * ((⌊Real.sqrt (N : ℝ) / c⌋₊ : ℕ) : ℝ) / Real.sqrt (N : ℝ))
      ≤ (Real.pi / 2) * 1 := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = Real.pi / 2 := mul_one _

/-- For positive `N` and `epsilon`, the scalar analog angle at `analogStepCount N epsilon` is at
most `pi/2`. -/
theorem analog_angle_at_stepCount_le {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    analogAngle N ε (analogStepCount N ε) ≤ Real.pi / 2 := by
  unfold analogAngle analogStepCount
  exact angle_at_stepCount_le hN hε

/-- For positive `N` and `epsilon`, the scalar adiabatic angle at `adiabaticStepCount N epsilon`
is at most `pi/2`. -/
theorem adiabatic_angle_at_stepCount_le {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    adiabaticAngle N ε (adiabaticStepCount N ε) ≤ Real.pi / 2 := by
  have hε3 : 0 < ε ^ 3 := by positivity
  unfold adiabaticAngle adiabaticStepCount
  exact angle_at_stepCount_le hN hε3

/-- For positive `N`, the scalar Grover angle at `groverStepCount N` is at most `pi/2`. -/
theorem grover_angle_at_stepCount_le {N : ℕ} (hN : 0 < N) :
    groverAngle N (groverStepCount N) ≤ Real.pi / 2 := by
  unfold groverAngle groverStepCount
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos_of_pos hNpos
  have hle : ((⌊(Real.pi / 4) * Real.sqrt (N : ℝ)⌋₊ : ℕ) : ℝ) ≤
      (Real.pi / 4) * Real.sqrt (N : ℝ) := Nat.floor_le (by positivity)
  have hmul : 2 * ((⌊(Real.pi / 4) * Real.sqrt (N : ℝ)⌋₊ : ℕ) : ℝ) /
      Real.sqrt (N : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hsqrt]
    nlinarith [hle]
  exact hmul

/-- On a nonempty finite search space, `j` Grover iterations advance the marked-vector angle
from `x` to `x + 2*j*theta`, retaining its common scale `u` [RolandCerf2003]. The
assumptions identify `sin(theta)^2` with the marked fraction and require both `sin(theta)`
and `cos(theta)` to be nonzero. -/
theorem grover_constant_angular_velocity {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ u : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) (x : ℝ) :
    Run (SetOracle A)
        (Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit I j)
        (Qatlib.Foundations.PureStateMath.Reflection.MarkedVector A
          (u * Real.sin x / Real.sin θ : ℂ) (u * Real.cos x / Real.cos θ : ℂ)) =
      Qatlib.Foundations.PureStateMath.Reflection.MarkedVector A
        (u * Real.sin (x + 2 * j * θ) / Real.sin θ : ℂ)
        (u * Real.cos (x + 2 * j * θ) / Real.cos θ : ℂ) :=
  Qatlib.Concepts.SearchStopping.KnownCount.run_groverCircuit_markedVector
    hN A θ u hθ hs hc j x

/-- The `j`-iteration Grover circuit on the Boolean index type uses exactly `j` oracle queries. -/
theorem grover_queryCount (j : ℕ) :
    QueryCount
      (Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit (Bool) j) = j :=
  Qatlib.Concepts.SearchStopping.KnownCount.queryCount_groverCircuit j

/-- The product of constant-Hamiltonian evolutions `exp(-i*t0*H0) * exp(-i*tf*Hf)`. Acting on a
state, it applies the `Hf` evolution first and the `H0` evolution second. -/
def hamStep {I : Type} [Fintype I] [DecidableEq I]
    (H0 Hf : Matrix I I ℂ) (t0 tf : ℝ) : Matrix I I ℂ :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
      (fun _ => Complex.I • H0) 0 t0 *
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
      (fun _ => Complex.I • Hf) 0 tf

/-- If `H0` and `Hf` are Hermitian, their composed Hamiltonian step is unitary for every pair of
real evolution times [RolandCerf2003]. -/
theorem hamStep_unitary {I : Type} [Fintype I] [DecidableEq I]
    (H0 Hf : Matrix I I ℂ) (h0 : H0.IsHermitian) (hf : Hf.IsHermitian)
    (t0 tf : ℝ) : hamStep H0 Hf t0 tf ∈ Matrix.unitaryGroup I ℂ := by
  unfold hamStep
  exact mul_mem
    (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
      I (fun _ => H0) continuous_const (fun _ => h0) 0 t0)
    (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
      I (fun _ => Hf) continuous_const (fun _ => hf) 0 tf)

/-- The diagonal Boolean gate multiplying the false basis state by `exp(-i*t)` and leaving the
true basis state fixed. -/
def phaseGate (t : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b =>
    if b then 1 else Complex.exp (-(Complex.I * (t : ℂ)))

/-- The tensor product of the identity on the search register with `phaseGate t` on the Boolean
ancilla. -/
def ancillaPhase {I : Type} [Fintype I] [DecidableEq I] (t : ℝ) :
    Matrix (I × Bool) (I × Bool) ℂ :=
  TensorGate (1 : Matrix I I ℂ) (phaseGate t)

/-- The circuit consisting, in execution order, of an oracle query, the ancilla phase gate, and
a second oracle query. For a bit oracle, the two queries compute and uncompute its Boolean
value around the phase operation [RolandCerf2003]. -/
def oracleHamStepCircuit {I : Type} [Fintype I] [DecidableEq I] (t : ℝ) :
    Circuit (I × Bool) :=
  [Step.query, Step.gate (ancillaPhase (I := I) t), Step.query]

/-- The oracle Hamiltonian step circuit uses exactly two oracle queries for every real time
parameter. -/
theorem queryCount_oracleHamStepCircuit {I : Type} [Fintype I] [DecidableEq I]
    (t : ℝ) : QueryCount (oracleHamStepCircuit (I := I) t) = 2 := rfl

/-- Applying the identity on the first register tensored with `V` applies `V` to each slice of
the second register while keeping the first index fixed. -/
private theorem applyGate_tensorGate_one_left {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V : Matrix J J ℂ) (χ : QState (I × J)) (i : I) (j : J) :
    ApplyGate (TensorGate (1 : Matrix I I ℂ) V) χ (i, j) = ∑ l, V j l * χ (i, l) := by
  simp only [ApplyGate, TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Matrix.mulVec,
    dotProduct]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Matrix.one_apply, if_neg (Ne.symm hk)]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The ancilla phase gate multiplies an amplitude by `exp(-i*t)` when its Boolean index is
false and by `1` when that index is true. -/
private theorem applyGate_ancillaPhase {I : Type} [Fintype I] [DecidableEq I]
    (t : ℝ) (χ : QState (I × Bool)) (i : I) (b : Bool) :
    ApplyGate (ancillaPhase (I := I) t) χ (i, b) =
      (if b then 1 else Complex.exp (-(Complex.I * (t : ℂ)))) * χ (i, b) := by
  unfold ancillaPhase phaseGate
  rw [applyGate_tensorGate_one_left]
  rw [Finset.sum_eq_single b]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

/-- With a false ancilla, the two-query circuit multiplies `psi x` by `1` when `f x` is true and
by `exp(-i*t)` when `f x` is false, returning the ancilla to false [RolandCerf2003]. -/
theorem run_oracleHamStepCircuit {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bool) (t : ℝ) (ψ : QState I) :
    Run (BitOracleOn f) (oracleHamStepCircuit (I := I) t)
        (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false)) =
      TensorState
        (fun x => (if f x then 1 else Complex.exp (-(Complex.I * (t : ℂ)))) * ψ x)
        (Qatlib.Foundations.PureStateMath.Ket false) := by
  funext p
  obtain ⟨x, b⟩ := p
  simp only [oracleHamStepCircuit, run_query, run_gate, run_nil]
  rw [applyGate_bitOracleOn]
  simp only [BitFlip]
  rw [applyGate_ancillaPhase, applyGate_bitOracleOn]
  cases hf : f x <;> cases b <;>
    simp [hf, TensorState, Qatlib.Foundations.PureStateMath.Ket, Bool.xor,
      BitFlip]

/-- Under the marked-fraction and nonzero sine/cosine assumptions, positive schedule parameters
`N` and `epsilon`, and Hermitian `H0` and `Hf`, this theorem collects exact Grover rotation
and query count, scalar schedule increments and angle bounds, Hamiltonian-step unitarity,
and the two-query ancilla implementation [RolandCerf2003]. Its analog and adiabatic
conclusions concern the scalar schedules defined here. -/
theorem main_constant_angular_velocity_and_circuit_implementation
    {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ u : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0)
    (N : ℕ) (hNpos : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (H0 Hf : Matrix I I ℂ) (h0 : H0.IsHermitian) (hf : Hf.IsHermitian)
    (f : I → Bool) (ψ : QState I) (t0 tf : ℝ) :
    (∀ (j : ℕ) (x : ℝ),
        Run (SetOracle A)
            (Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit I j)
            (Qatlib.Foundations.PureStateMath.Reflection.MarkedVector A
              (u * Real.sin x / Real.sin θ : ℂ) (u * Real.cos x / Real.cos θ : ℂ)) =
          Qatlib.Foundations.PureStateMath.Reflection.MarkedVector A
            (u * Real.sin (x + 2 * j * θ) / Real.sin θ : ℂ)
            (u * Real.cos (x + 2 * j * θ) / Real.cos θ : ℂ)) ∧
    (∀ j : ℕ,
        QueryCount
          (Qatlib.Concepts.SearchStopping.KnownCount.GroverCircuit I j) = j) ∧
    (∀ j : ℕ, analogAngle N ε (j + 1) = analogAngle N ε j + analogIncrement N ε) ∧
    (∀ j : ℕ, adiabaticAngle N ε (j + 1) = adiabaticAngle N ε j + adiabaticIncrement N ε) ∧
    (adiabaticDt0 ε 0 + adiabaticDtf ε 0 = ε ^ 2 * (Real.pi / 2)) ∧
    (analogAngle N ε (analogStepCount N ε) ≤ Real.pi / 2) ∧
    (adiabaticAngle N ε (adiabaticStepCount N ε) ≤ Real.pi / 2) ∧
    (hamStep H0 Hf t0 tf ∈ Matrix.unitaryGroup I ℂ) ∧
    (QueryCount (oracleHamStepCircuit (I := I) tf) = 2) ∧
    (Run (BitOracleOn f) (oracleHamStepCircuit (I := I) tf)
        (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false)) =
      TensorState
        (fun x => (if f x then 1 else Complex.exp (-(Complex.I * (tf : ℂ)))) * ψ x)
        (Qatlib.Foundations.PureStateMath.Ket false)) := by
  refine ⟨grover_constant_angular_velocity hN A θ u hθ hs hc,
    fun j => Qatlib.Concepts.SearchStopping.KnownCount.queryCount_groverCircuit
      (I := I) j,
    analogAngle_succ N ε, adiabaticAngle_succ N ε, adiabatic_dt_add ε 0,
    analog_angle_at_stepCount_le hNpos hε, adiabatic_angle_at_stepCount_le hNpos hε,
    hamStep_unitary H0 Hf h0 hf t0 tf, queryCount_oracleHamStepCircuit tf,
    run_oracleHamStepCircuit f tf ψ⟩

end Qatlib.Papers.HamGrover03.MainResults
