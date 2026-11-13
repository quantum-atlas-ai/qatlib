/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffectiveDefs

/-!
# Effective phase and execution identities

This module proves quotient–remainder identities for rational-angle dyadic approximations and a
local error bound for complex phases. It also verifies basis-state execution and workspace
accounting for `copyProgram`, and relates the forward and reverse local transition matrices by
conjugate transpose, using the circuit and amplitude conventions of [NielsenChuang2010].

The Section 8 ledger records the two-level and parameter-count inequalities used alongside these
implementation identities.

## Main statements

* `thresholdGoal_phase_error`: phase error is bounded by twice the angle error under the stated
  margin.
* `clause11_copy_program_quantum`: the extracted quantum circuit agrees with the live-register
  interpreter.
* `clause11_alloc_peak_workspace`: one allocation beyond the base range has peak workspace one.
* `clause12_two_way_window`: powers of the reverse transition matrix are adjoints of forward
  powers.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Matrix
open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitImpl.GateSynthesis
open scoped Classical BigOperators ENNReal

/-- The dyadic quotient and remainder satisfy `a.den * dyadicApprox a d + dyadicRemainder a d =
a.num * 2 ^ d`. -/
theorem thresholdGoal_dyadic_remainder (a : RatAngle) (d : ℕ) :
    a.den * (dyadicApprox a d) + dyadicRemainder a d = a.num * 2 ^ d := by
  have h := Nat.div_add_mod (a.num * 2 ^ d) a.den
  unfold dyadicApprox dyadicRemainder
  exact h

/-- The dyadic remainder is strictly smaller than the positive denominator of the rational
angle. -/
theorem thresholdGoal_dyadic_remainder_lt (a : RatAngle) (d : ℕ) :
    dyadicRemainder a d < a.den := Nat.mod_lt _ a.den_pos

/-- The dyadic quotient–remainder identity remains valid after casting all terms to the real
numbers. -/
theorem thresholdGoal_dyadic_error_identity (a : RatAngle) (d : ℕ) :
    (a.den : ℝ) * (dyadicApprox a d : ℝ) + (dyadicRemainder a d : ℝ)
      = (a.num : ℝ) * (2 : ℝ) ^ d := by
  have h1 : (a.den : ℝ) * (dyadicApprox a d : ℝ)
      = ((a.den * (dyadicApprox a d) : ℕ) : ℝ) := by norm_cast
  have h2 : (dyadicRemainder a d : ℝ) = ((dyadicRemainder a d : ℕ) : ℝ) := rfl
  have h3 : (a.num : ℝ) * (2 : ℝ) ^ d = ((a.num * 2 ^ d : ℕ) : ℝ) := by norm_cast
  rw [h1, h2, h3]
  exact_mod_cast (thresholdGoal_dyadic_remainder a d)

/-- When two real angles differ by at most one, the norm of the difference of their complex
phases is at most twice their absolute difference. -/
theorem thresholdGoal_phase_lipschitz (θ φ : ℝ) (h : |θ - φ| ≤ 1) :
    ‖phaseOf θ - phaseOf φ‖ ≤ 2 * |θ - φ| := by
  have hfac : phaseOf θ - phaseOf φ
      = phaseOf φ * (phaseOf (θ - φ) - 1) := by
    have he : phaseOf θ = phaseOf φ * phaseOf (θ - φ) := by
      simp only [phaseOf]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  have hnorm : ‖phaseOf φ‖ = 1 := by
    simp only [phaseOf, Complex.norm_exp, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re, sub_zero, mul_zero, zero_mul,
      Real.exp_zero]
  rw [hfac, Complex.norm_mul, hnorm]
  simp only [phaseOf, one_mul]
  have h2 := Complex.norm_exp_sub_one_le (x := Complex.I * ((θ - φ : ℝ) : ℂ)) (by
    rw [Complex.norm_mul, Complex.norm_I, Complex.norm_real]
    simpa using! h)
  calc ‖Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1‖
      ≤ 2 * ‖Complex.I * ((θ - φ : ℝ) : ℂ)‖ := h2
    _ = 2 * |θ - φ| := by
      rw [Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      norm_num

/-- If the rational angle and its dyadic approximation differ by at most one, their phase
difference is at most twice the angle error. -/
theorem thresholdGoal_phase_error (a : RatAngle) (d : ℕ)
    (hmargin : |a.value - dyadicValue a d| ≤ 1) :
    ‖phaseOf a.value - phaseOf (dyadicValue a d)‖ ≤ 2 * |a.value - dyadicValue a d| :=
  thresholdGoal_phase_lipschitz a.value (dyadicValue a d) hmargin

/-- For distinct in-range input and work wires, the gates extracted from `copyProgram` form a
valid classical gate word. -/
theorem clause11_copy_program_classical {N : ℕ} {inW work : ℕ}
    (hin : inW < N) (hwork : work < N) (hne : inW ≠ work) :
    classicalWord N (opsGates (copyProgram inW work)) := by
  simp only [copyProgram, opsGates, classicalWord, classicalCodeOk]
  exact ⟨⟨hin, hwork, hne⟩, ⟨⟨hin, hwork, hne⟩, trivial⟩⟩

/-- For distinct in-range input and work wires, the quantum circuit extracted from `copyProgram`
agrees on basis states with `liveRun` initialized at the base live-wire list. -/
theorem clause11_copy_program_quantum {N : ℕ} {base inW work : ℕ}
    (hin : inW < N) (hwork : work < N) (hne : inW ≠ work) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (finiteCodeCircuit N (opsGates (copyProgram inW work)))
        (Ket x) =
      Ket (liveRun base (copyProgram inW work) ⟨x, List.range base⟩).bits :=
  walkGoal_live_wire_quantum_semantics base (copyProgram inW work) x (List.range base)
    (clause11_copy_program_classical hin hwork hne)

/-- Starting with the live-wire list `List.range base`, a single allocation at an index at least
`base` has peak workspace one. -/
theorem clause11_alloc_peak_workspace {N : ℕ} {base w : ℕ} (hbase : base ≤ w) (x : Reg N) :
    livePeakWorkspace base [DynOp.alloc w] ⟨x, List.range base⟩ = 1 := by
  have hnotmem : w ∉ List.range base := by
    simp only [List.mem_range]
    omega
  simp [livePeakWorkspace, liveTrace, liveStep, hbase, hnotmem]

/-- The function `vonNeumannOut` returns the common bit on the two equal-bit pairs and returns
`none` on the two unequal-bit pairs. -/
theorem clause11_von_neumann_prefixes :
    vonNeumannOut [false, false] = some false ∧
    vonNeumannOut [true, true] = some true ∧
    vonNeumannOut [false, true] = none ∧
    vonNeumannOut [true, false] = none := by
  simp [vonNeumannOut]

/-- For positive `n`, the lower two-level count, Section 8 count, and unitary parameter count
satisfy the stated comparisons with `4 ^ n`. -/
theorem clause12_section8_ledger (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * reckTwoLevelLower n ∧
    section8TwoLevelCount n ≤ 4 ^ n ∧
    unitaryParamCount (2 ^ n) = 4 ^ n := by
  obtain ⟨h1, _, h3⟩ := section8TwoLevelCount_bounds n hn
  exact ⟨h1, h3, unitaryParamCount_two_pow n⟩

/-- The reverse local transition matrix is the conjugate transpose of the forward local
transition matrix. -/
theorem clause12_reverse_transition_adjoint {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) :
    qtmReverseTransition m = (qtmTransition m)ᴴ := by
  ext i j
  simp only [qtmReverseTransition, qtmTransition, Matrix.conjTranspose_apply]

/-- Every natural power of the reverse local transition matrix is the conjugate transpose of the
corresponding forward power. -/
theorem clause12_two_way_window {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) (k : ℕ) :
    (qtmReverseTransition m) ^ k = ((qtmTransition m) ^ k)ᴴ := by
  rw [Matrix.conjTranspose_pow]
  rw [clause12_reverse_transition_adjoint m]

/-- The selected reverse transition power entry equals the conjugate of the forward power entry
with row `(qf, a)` and column `(m.start, m.blank)`. -/
theorem clause12_reverse_acceptance_conjugate {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) :
    windowReverseAcceptance m k qf a
      = star (((qtmTransition m) ^ k) (qf, a) (m.start, m.blank)) := by
  unfold windowReverseAcceptance
  rw [clause12_two_way_window m k]
  simp [Matrix.conjTranspose_apply]

end Qatlib.Concepts.CircuitImpl.GateSynthesis

end
