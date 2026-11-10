/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks
import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.TwoLevelSynthesis
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem inv_sqrt2_mul_complex :
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = (1/2 : ℂ) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [← mul_inv, hs]
  norm_num

theorem hadamard_conj_pauliZ : Hadamard * PauliZ * Hadamard = PauliX := by
  ext a b
  cases a <;> cases b <;>
    simp [Hadamard, PauliZ, PauliX, permMatrix, Matrix.mul_apply] <;>
    rw [inv_sqrt2_mul_complex] <;> norm_num

theorem hadamard_mul_self : Hadamard * Hadamard = (1 : Matrix Bool Bool ℂ) := by
  ext a b
  cases a <;> cases b <;>
    simp [Hadamard, Matrix.mul_apply] <;>
    rw [inv_sqrt2_mul_complex] <;> norm_num

theorem hadamard_unit : IsUnit (Hadamard : Matrix Bool Bool ℂ) :=
  isUnit_iff_exists_inv.mpr ⟨Hadamard, hadamard_mul_self⟩

theorem hadamard_inv : (Hadamard : Matrix Bool Bool ℂ)⁻¹ = Hadamard :=
  Matrix.inv_eq_right_inv hadamard_mul_self

theorem Rz_eq_smul_exp (θ : ℝ) :
    Rz θ = (Complex.exp ((θ/2 : ℝ) * Complex.I)) • NormedSpace.exp
      ((-(Complex.I) * ((θ/2 : ℝ) : ℂ)) • PauliZ) := by
  rw [PauliZ, ← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  ext a b
  cases a <;> cases b <;>
    simp [Rz, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      ← Complex.exp_eq_exp_ℂ]
  · rw [← Complex.exp_add]
    rw [show (↑θ / 2 * Complex.I + -(Complex.I * (↑θ / 2))) = 0 from by ring,
      Complex.exp_zero]
  · rw [← Complex.exp_add]
    congr 1
    ring

theorem hadamard_expZ_hadamard (φ : ℂ) :
    Hadamard * NormedSpace.exp (φ • PauliZ) * Hadamard =
      NormedSpace.exp (φ • PauliX) := by
  have hconj := Matrix.exp_conj Hadamard (φ • PauliZ) hadamard_unit
  rw [hadamard_inv] at hconj
  rw [← hconj]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, hadamard_conj_pauliZ]

theorem xEvol_eq (t τ : ℝ) :
    HamiltonianEvolution ((t : ℂ) • PauliX) τ =
      (Complex.exp ((-(τ*t) : ℝ) * Complex.I)) •
        (Hadamard * Rz (2*τ*t) * Hadamard) := by
  have hθ : ((2*τ*t : ℝ)/2 : ℝ) = τ*t := by ring
  rw [Rz_eq_smul_exp, hθ]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hadamard_expZ_hadamard]
  unfold HamiltonianEvolution
  rw [show ((-(Complex.I) * ((τ : ℝ) : ℂ)) • (((t : ℝ) : ℂ) • PauliX))
      = ((-(Complex.I) * (((τ*t : ℝ)) : ℂ)) • PauliX) from by
    rw [smul_smul]
    congr 1
    push_cast
    ring]
  rw [← Complex.exp_add]
  have hzero : (↑(-(τ*t)) : ℂ) * Complex.I + ↑(τ*t) * Complex.I = 0 := by
    push_cast
    ring
  rw [hzero, Complex.exp_zero, one_smul]

def globalPhase (I : Type*) [Fintype I] [DecidableEq I] (φ : ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun _ => Complex.exp (φ * Complex.I))

theorem diagonal_unitary {J : Type*} [Fintype J] [DecidableEq J]
    (f : J → ℂ) (hf : ∀ x, Complex.normSq (f x) = 1) :
    Matrix.diagonal f ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h : (fun i => (star f) i * f i) = (fun _ => (1 : ℂ)) := by
    funext i
    rw [Pi.star_apply, show star (f i) = (starRingEnd ℂ) (f i) from rfl,
      ← Complex.normSq_eq_conj_mul_self, hf i]
    rfl
  rw [h, Matrix.diagonal_one]

theorem normSq_exp_I (φ : ℝ) : Complex.normSq (Complex.exp (φ * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp

theorem globalPhase_unitary (I : Type*) [Fintype I] [DecidableEq I] (φ : ℝ) :
    globalPhase I φ ∈ Matrix.unitaryGroup I ℂ := by
  unfold globalPhase
  exact diagonal_unitary _ (fun _ => normSq_exp_I φ)

theorem hadamard_unitary : Hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  have hstar : (star Hadamard : Matrix Bool Bool ℂ) = Hadamard := by
    ext a b
    cases a <;> cases b <;>
      simp [Hadamard, Matrix.star_apply]
  rw [Matrix.mem_unitaryGroup_iff', hstar, hadamard_mul_self]

theorem Rz_unitary (θ : ℝ) : Rz θ ∈ Matrix.unitaryGroup Bool ℂ := by
  apply diagonal_unitary
  intro a
  cases a
  · simp
  · simpa [Rz] using! normSq_exp_I θ

theorem blockDiagonal_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix Bool Bool ℂ} (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    Matrix.blockDiagonal (fun _ : ι => U) ∈ Matrix.unitaryGroup (Bool × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hfun : (fun i : ι => (U : Matrix Bool Bool ℂ)ᴴ * U) = (fun _ => (1 : Matrix Bool Bool ℂ)) := by
    funext i
    simpa [Matrix.star_eq_conjTranspose] using! hU
  rw [hfun]
  exact Matrix.blockDiagonal_one

def blockWord (k : ℕ) (t time : ℝ) : Circuit (Bool × Fin k) :=
  [ .gate (Matrix.blockDiagonal (fun _ : Fin k => Hadamard)),
    .gate (Matrix.blockDiagonal (fun _ : Fin k => Rz (2*time*t))),
    .gate (Matrix.blockDiagonal (fun _ : Fin k => Hadamard)),
    .gate (Matrix.blockDiagonal (fun _ : Fin k => globalPhase Bool (-(time*t)))) ]

theorem blockU_eq_four (k : ℕ) (t time : ℝ) :
    ParallelBlocks.blockU k t time =
      Matrix.blockDiagonal (fun _ : Fin k => globalPhase Bool (-(time*t))) *
        Matrix.blockDiagonal (fun _ : Fin k => Hadamard) *
        Matrix.blockDiagonal (fun _ : Fin k => Rz (2*time*t)) *
        Matrix.blockDiagonal (fun _ : Fin k => Hadamard) := by
  rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  rw [ParallelBlocks.blockU]
  congr 1
  funext j
  rw [ParallelBlocks.localU, ParallelBlocks.localH, xEvol_eq]
  rw [globalPhase, ← Matrix.smul_one_eq_diagonal]
  simp only [Matrix.smul_mul, Matrix.one_mul]

theorem blockWord_correct (k : ℕ) (t time : ℝ) (ψ : QState (Bool × Fin k)) :
    Run 1 (blockWord k t time) ψ = ApplyGate (ParallelBlocks.blockU k t time) ψ ∧
      IsUnitaryCircuit (blockWord k t time) ∧
      QueryCount (blockWord k t time) = 0 ∧
      GateCount (blockWord k t time) = 4 := by
  have hu : IsUnitaryCircuit (blockWord k t time) := by
    intro U hU
    simp only [blockWord, List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with h | h | h | h
    · cases h; exact blockDiagonal_unitary hadamard_unitary
    · cases h; exact blockDiagonal_unitary (Rz_unitary _)
    · cases h; exact blockDiagonal_unitary hadamard_unitary
    · cases h; exact blockDiagonal_unitary (diagonal_unitary _ (fun _ => normSq_exp_I _))
  refine ⟨?_, hu, rfl, rfl⟩
  rw [blockU_eq_four]
  simp only [blockWord, Run, run_gate]
  rw [← applyGate_mul, ← applyGate_mul, ← applyGate_mul]

theorem quWordBits_log_bounds (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m : ℝ) / Real.log 2 ≤ (quWordBits m : ℝ) ∧
      (quWordBits m : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hle : m ≤ 2 ^ quWordBits m := le_two_pow_quWordBits m
  have hlower : Real.log (m : ℝ) / Real.log 2 ≤ (quWordBits m : ℝ) := by
    have hlog : Real.log (m : ℝ) ≤ Real.log ((2 : ℝ) ^ quWordBits m) :=
      Real.log_le_log hpos (by exact_mod_cast hle)
    rw [Real.log_pow] at hlog
    rw [div_le_iff₀ hlog2]
    simpa [mul_comm] using! hlog
  refine ⟨hlower, ?_⟩
  set q := quWordBits m with hqdef
  by_cases hq : q = 0
  · have hm1 : m = 1 := le_antisymm (by simpa [hq] using! hle) hm
    rw [hm1, hq]
    simp
  · have hqpos : 1 ≤ q := Nat.pos_of_ne_zero hq
    have hfalse : ¬ m ≤ 2 ^ (q - 1) := by
      intro h
      have hc := Nat.clog_le_iff_le_pow (b := 2) (by norm_num : 1 < 2) (x := m) (y := q - 1)
      have hcq : quWordBits m ≤ q - 1 := hc.mpr h
      rw [hqdef] at hcq hqpos
      omega
    have hlt : 2 ^ (q - 1) < m := by
      have := Nat.lt_of_not_ge hfalse
      simpa using! this
    have hlog : Real.log ((2 : ℝ) ^ (q - 1)) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hlt.le)
    rw [Real.log_pow] at hlog
    rw [Nat.cast_sub hqpos] at hlog
    have hdiv : ((q : ℝ) - 1) ≤ Real.log (m : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      simpa [mul_comm] using! hlog
    linarith

end Qatlib.Papers.ManyBodyFermi97.MainResults.TwoLevelSynthesis
