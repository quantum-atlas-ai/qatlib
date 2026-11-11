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

/-!
# Pauli-Z and tensor rotation realization

The encoding `zWord` turns a Boolean word into an identity/Z Pauli word. Its diagonal entries
are the Walsh character, so `walsh_generator_pauli_sum` realizes each Walsh phase generator as a
diagonal Pauli-Z expansion and `walshCoeff_eq_pauli_trace` identifies its coefficient by a
normalized trace.

The construction `tensorRzProduct` uses actual one-qubit `Rz` matrices. The result
`source_rz_eq_gate_tensor` relates the phase ansatz to their tensor product with an explicit
global phase, connecting the formal phase model to the rotation family in [ZhangEtAl2026].

## Main statements

- `pauliWord_eq_walsh` identifies Pauli-Z words with diagonal Walsh characters.
* `walsh_generator_pauli_sum` and `walshCoeff_eq_pauli_trace` give the generator expansion and
  coefficient formula.
- `tensorRzProduct_eq` identifies the rotation tensor product with its diagonal phase function.
* `source_rz_eq_gate_tensor` computes the global phase relating the source ansatz to actual
  gates.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

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

/-- The entrywise tensor product of a finite family of diagonal two-level matrices is diagonal,
with diagonal entries equal to the products of their local diagonal entries. -/
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

/-- The encoding `zWord` places `Z` at each true coordinate of a Boolean word and the identity
at each false coordinate. -/
def zWord {n : ℕ} (s : Cube n) : Fin n → Fin 4 := fun j => if s j then 3 else 0

/-- An identity or Pauli-Z matrix is diagonal with the corresponding local Walsh sign on its
diagonal. -/
theorem local_z_diagonal (a : Bool) :
    pauliBool (if a then (3:Fin 4) else 0) =
      Matrix.diagonal (fun b : Bool => ((if a then (if b then -1 else 1) else 1 : ℝ):ℂ)) := by
  cases a <;> ext x y <;> cases x <;> cases y <;>
    norm_num [pauliBool, PauliZ]

/-- The Pauli matrix encoded by `zWord s` is the diagonal matrix of the Walsh character indexed
by `s`. -/
theorem pauliWord_eq_walsh {n : ℕ} (s : Cube n) :
    pauliWord (zWord s)=Matrix.diagonal (fun x : Cube n => (walsh s x:ℂ)) := by
  unfold pauliWord zWord
  simp_rw [local_z_diagonal]
  rw [tensor_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  simp only [walsh, Complex.ofReal_prod]

/-- The diagonal matrix of `walshPhase alpha` equals the sum of the corresponding identity/Z
Pauli words weighted by `alpha`. -/
theorem walsh_generator_pauli_sum {n : ℕ} (α : Cube n → ℝ) :
    Matrix.diagonal (fun x : Cube n => (walshPhase α x:ℂ)) =
      ∑ s : Cube n, (α s:ℂ) • pauliWord (zWord s) := by
  simp_rw [pauliWord_eq_walsh]
  ext x y
  by_cases hxy : x=y
  · subst y
    simp [Matrix.sum_apply, Matrix.smul_apply, walshPhase, Complex.ofReal_sum]
  · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy]

/-- A real function's Walsh coefficient is the normalized trace of its diagonal matrix
multiplied by the corresponding Pauli-Z word, after casting to complex numbers. -/
theorem walshCoeff_eq_pauli_trace {n : ℕ} (f : Cube n → ℝ) (s : Cube n) :
    (walshCoeff f s:ℂ)=((2:ℂ)^n)⁻¹ * Matrix.trace
      (Matrix.diagonal (fun x : Cube n => (f x:ℂ)) * pauliWord (zWord s)) := by
  rw [pauliWord_eq_walsh, Matrix.diagonal_mul_diagonal]
  simp [walshCoeff, cubeAvg, Matrix.trace, Complex.ofReal_sum]

/-- The matrix `tensorRzProduct theta` is the tensor product of the one-qubit `Rz` matrices with
angles specified by `theta`, expressed entrywise on the Boolean register. -/
def tensorRzProduct {n : ℕ} (θ : Fin n → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y => ∏ j, Rz (θ j) (x j) (y j)

/-- The tensor product of actual `Rz` gates equals the diagonal unitary associated with
`lowPhase 0 theta`. -/
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

/-- The source rotation ansatz equals the tensor product of actual `Rz` gates multiplied by the
global phase with angle `phi - sum_j theta_j / 2`. This identifies the gate family used for
the phase approximation in [ZhangEtAl2026]. -/
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
