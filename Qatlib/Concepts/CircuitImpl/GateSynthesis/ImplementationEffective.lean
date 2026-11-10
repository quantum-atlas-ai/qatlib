/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffectiveDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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

theorem thresholdGoal_dyadic_remainder (a : RatAngle) (d : ℕ) :
    a.den * (dyadicApprox a d) + dyadicRemainder a d = a.num * 2 ^ d := by
  have h := Nat.div_add_mod (a.num * 2 ^ d) a.den
  unfold dyadicApprox dyadicRemainder
  exact h

theorem thresholdGoal_dyadic_remainder_lt (a : RatAngle) (d : ℕ) :
    dyadicRemainder a d < a.den := Nat.mod_lt _ a.den_pos

theorem thresholdGoal_dyadic_error_identity (a : RatAngle) (d : ℕ) :
    (a.den : ℝ) * (dyadicApprox a d : ℝ) + (dyadicRemainder a d : ℝ)
      = (a.num : ℝ) * (2 : ℝ) ^ d := by
  have h1 : (a.den : ℝ) * (dyadicApprox a d : ℝ)
      = ((a.den * (dyadicApprox a d) : ℕ) : ℝ) := by norm_cast
  have h2 : (dyadicRemainder a d : ℝ) = ((dyadicRemainder a d : ℕ) : ℝ) := rfl
  have h3 : (a.num : ℝ) * (2 : ℝ) ^ d = ((a.num * 2 ^ d : ℕ) : ℝ) := by norm_cast
  rw [h1, h2, h3]
  exact_mod_cast (thresholdGoal_dyadic_remainder a d)

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

theorem thresholdGoal_phase_error (a : RatAngle) (d : ℕ)
    (hmargin : |a.value - dyadicValue a d| ≤ 1) :
    ‖phaseOf a.value - phaseOf (dyadicValue a d)‖ ≤ 2 * |a.value - dyadicValue a d| :=
  thresholdGoal_phase_lipschitz a.value (dyadicValue a d) hmargin

theorem clause11_copy_program_classical {N : ℕ} {inW work : ℕ}
    (hin : inW < N) (hwork : work < N) (hne : inW ≠ work) :
    classicalWord N (opsGates (copyProgram inW work)) := by
  simp only [copyProgram, opsGates, classicalWord, classicalCodeOk]
  exact ⟨⟨hin, hwork, hne⟩, ⟨⟨hin, hwork, hne⟩, trivial⟩⟩

theorem clause11_copy_program_quantum {N : ℕ} {base inW work : ℕ}
    (hin : inW < N) (hwork : work < N) (hne : inW ≠ work) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (finiteCodeCircuit N (opsGates (copyProgram inW work)))
        (Ket x) =
      Ket (liveRun base (copyProgram inW work) ⟨x, List.range base⟩).bits :=
  walkGoal_live_wire_quantum_semantics base (copyProgram inW work) x (List.range base)
    (clause11_copy_program_classical hin hwork hne)

theorem clause11_alloc_peak_workspace {N : ℕ} {base w : ℕ} (hbase : base ≤ w) (x : Reg N) :
    livePeakWorkspace base [DynOp.alloc w] ⟨x, List.range base⟩ = 1 := by
  have hnotmem : w ∉ List.range base := by
    simp only [List.mem_range]
    omega
  simp [livePeakWorkspace, liveTrace, liveStep, hbase, hnotmem]

theorem clause11_von_neumann_prefixes :
    vonNeumannOut [false, false] = some false ∧
    vonNeumannOut [true, true] = some true ∧
    vonNeumannOut [false, true] = none ∧
    vonNeumannOut [true, false] = none := by
  simp [vonNeumannOut]

theorem clause12_section8_ledger (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * reckTwoLevelLower n ∧
    section8TwoLevelCount n ≤ 4 ^ n ∧
    unitaryParamCount (2 ^ n) = 4 ^ n := by
  obtain ⟨h1, _, h3⟩ := section8TwoLevelCount_bounds n hn
  exact ⟨h1, h3, unitaryParamCount_two_pow n⟩

theorem clause12_reverse_transition_adjoint {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) :
    qtmReverseTransition m = (qtmTransition m)ᴴ := by
  ext i j
  simp only [qtmReverseTransition, qtmTransition, Matrix.conjTranspose_apply]

theorem clause12_two_way_window {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) (k : ℕ) :
    (qtmReverseTransition m) ^ k = ((qtmTransition m) ^ k)ᴴ := by
  rw [Matrix.conjTranspose_pow]
  rw [clause12_reverse_transition_adjoint m]

theorem clause12_reverse_acceptance_conjugate {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) :
    windowReverseAcceptance m k qf a
      = star (((qtmTransition m) ^ k) (qf, a) (m.start, m.blank)) := by
  unfold windowReverseAcceptance
  rw [clause12_two_way_window m k]
  simp [Matrix.conjTranspose_apply]

end Qatlib.Concepts.CircuitImpl.GateSynthesis

end
