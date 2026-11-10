/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliBasis
import Qatlib.Papers.KoopmanSim26.SpectralRep.UniversalApproximation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.PauliClifford.PauliBasis
open Qatlib.Papers.KoopmanSim26.SpectralRep

namespace Qatlib.Papers.KoopmanSim26.SpectralRep.PauliBridge

theorem tensor_diagonal {n : ℕ} (d : Fin n → Bool → ℂ) :
    (fun x y : Reg n => ∏ j, (Matrix.diagonal (d j)) (x j) (y j)) =
      Matrix.diagonal (fun x : Reg n => ∏ j, d j (x j)) := by
  ext x y
  by_cases hxy : x=y
  · subst y
    simp
  · rw [Matrix.diagonal_apply_ne _ hxy]
    obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := by
      by_contra hn
      push Not at hn
      exact hxy (funext hn)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ hj

def zWord {n : ℕ} (s : Cube n) : Fin n → Fin 4 := fun j => if s j then 3 else 0

theorem local_z_diagonal (a : Bool) :
    pauliBool (if a then (3:Fin 4) else 0) =
      Matrix.diagonal (fun b : Bool => ((if a then (if b then -1 else 1) else 1 : ℝ):ℂ)) := by
  cases a <;> ext x y <;> cases x <;> cases y <;>
    norm_num [pauliBool, PauliZ]

theorem pauliWord_eq_walsh {n : ℕ} (s : Cube n) :
    pauliWord (zWord s)=Matrix.diagonal (fun x : Cube n => (walsh s x:ℂ)) := by
  unfold pauliWord zWord
  simp_rw [local_z_diagonal]
  rw [tensor_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  simp only [walsh, Complex.ofReal_prod]

theorem walsh_generator_pauli_sum {n : ℕ} (α : Cube n → ℝ) :
    Matrix.diagonal (fun x : Cube n => (walshPhase α x:ℂ)) =
      ∑ s : Cube n, (α s:ℂ) • pauliWord (zWord s) := by
  simp_rw [pauliWord_eq_walsh]
  ext x y
  by_cases hxy : x=y
  · subst y
    simp [Matrix.sum_apply, Matrix.smul_apply, walshPhase, Complex.ofReal_sum]
  · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy]

theorem walshCoeff_eq_pauli_trace {n : ℕ} (f : Cube n → ℝ) (s : Cube n) :
    (walshCoeff f s:ℂ)=((2:ℂ)^n)⁻¹ * Matrix.trace
      (Matrix.diagonal (fun x : Cube n => (f x:ℂ)) * pauliWord (zWord s)) := by
  rw [pauliWord_eq_walsh, Matrix.diagonal_mul_diagonal]
  simp [walshCoeff, cubeAvg, Matrix.trace, Complex.ofReal_sum]

def tensorRzProduct {n : ℕ} (θ : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y => ∏ j, Rz (θ j) (x j) (y j)

theorem tensorRzProduct_eq {n : ℕ} (θ : Fin n → ℝ) :
    tensorRzProduct θ=diagonalUnitary (lowPhase 0 θ) := by
  unfold tensorRzProduct Rz
  rw [tensor_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  unfold lowPhase
  simp only [zero_add]
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> simp [mul_comm]

theorem source_rz_eq_gate_tensor {n : ℕ} (φ : ℝ) (θ : Fin n → ℝ) :
    rzProductMatrix φ θ=phaseValue (φ-∑ j,θ j/2) • tensorRzProduct θ := by
  rw [rzProductMatrix_eq, tensorRzProduct_eq]
  ext x y
  by_cases hxy : x=y
  · subst y
    simp only [diagonalUnitary, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    have he : lowPhase (φ-∑ j,θ j/2) θ x = (φ-∑ j,θ j/2)+lowPhase 0 θ x := by
      simp only [lowPhase, zero_add]
    rw [he]
    simp only [phaseValue, Complex.ofReal_add, mul_add, Complex.exp_add]
  · simp [diagonalUnitary, Matrix.diagonal_apply_ne _ hxy]

end Qatlib.Papers.KoopmanSim26.SpectralRep.PauliBridge
