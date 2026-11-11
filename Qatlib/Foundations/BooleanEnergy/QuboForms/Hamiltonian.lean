/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.QuboForms.Quadratic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Diagonal Hamiltonians of Boolean quadratic forms

This module represents optional Boolean slots by diagonal operators and constructs the
Hamiltonian of a real quadratic form. Computational basis vectors have the corresponding
classical energies, and the expectation formula proves equivalence between classical minima and
basis-state ground expectations, supporting the annealing formulation of [SuksmonoMinato2019].

## Main statements

* `hamiltonian_diagonal`: Identify the energy diagonal.
* `expectation_eq_weighted`: Express expectations as weighted classical energies.
* `basis_quantum_ground_iff`: Relate basis-state and classical ground conditions.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.QuboForms

/-- The diagonal operator whose entries evaluate an optional variable slot, with `none`
representing the constant slot. -/
def slotOperator {V : Type*} [Fintype V] [DecidableEq V] (i : Option V) :
    Matrix (V → Bool) (V → Bool) ℂ := Matrix.diagonal (fun x => (slot x i : ℂ))

/-- The diagonal Pauli-Z operator acting by the spin of the Boolean variable `v`. -/
def pauliZ {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.diagonal (fun x => (HadamardGram.spin (x v) : ℂ))

/-- The number operator for variable `v` is one half of the identity minus its Pauli-Z operator. -/
theorem number_from_pauli {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    slotOperator (some v) = (1/2:ℂ) • (1-pauliZ v) := by
  ext x y
  by_cases h : x=y
  · subst y
    simp [slotOperator,pauliZ,slot,HadamardGram.spin,Matrix.smul_apply]
  · simp [slotOperator,pauliZ,Matrix.smul_apply,h]

/-- The operator of the constant slot is the identity matrix. -/
theorem slotOperator_none {V : Type*} [Fintype V] [DecidableEq V] :
    slotOperator (V:=V) none = 1 := by
  simp [slotOperator,slot,Matrix.diagonal_one]

/-- The diagonal Hamiltonian obtained by replacing the two slots in each quadratic coefficient
with their slot operators. -/
def hamiltonian {V : Type*} [Fintype V] [DecidableEq V] (a : Quadratic V) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  ∑ ij : Option V × Option V, (a ij : ℂ) • (slotOperator ij.1 * slotOperator ij.2)

/-- The Hamiltonian is diagonal, with each diagonal entry equal to the quadratic energy of the
corresponding Boolean configuration. -/
theorem hamiltonian_diagonal {V : Type*} [Fintype V] [DecidableEq V] (a : Quadratic V) :
    hamiltonian a = Matrix.diagonal (fun x => (quadraticEval x a : ℂ)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [hamiltonian,slotOperator,Matrix.diagonal_mul_diagonal,quadraticEval,
      Complex.ofReal_sum,Complex.ofReal_mul,Matrix.sum_apply,Matrix.smul_apply,mul_assoc]
  · simp [hamiltonian,slotOperator,Matrix.diagonal_mul_diagonal,h,Matrix.sum_apply,Matrix.smul_apply]

/-- The Hamiltonian associated with a real quadratic coefficient array is Hermitian. -/
theorem hamiltonian_hermitian {V : Type*} [Fintype V] [DecidableEq V] (a : Quadratic V) :
    (hamiltonian a).IsHermitian := by
  rw [hamiltonian_diagonal,Matrix.isHermitian_diagonal_iff]
  intro x
  simp [IsSelfAdjoint]

/-- The computational basis vector supported at the Boolean configuration `x`, with value one
there. -/
def basisState {V : Type*} [Fintype V] [DecidableEq V] (x : V → Bool) : (V → Bool) → ℂ :=
    Pi.single x 1

/-- Every computational basis vector is nonzero. -/
theorem basisState_ne_zero {V : Type*} [Fintype V] [DecidableEq V] (x : V → Bool) :
    basisState x ≠ 0 := by
  intro h
  have hx := congrFun h x
  simp [basisState] at hx

/-- The basis vector of a Boolean configuration satisfies the Hamiltonian eigenvalue equation
with that configuration's quadratic energy. -/
theorem basis_eigen_equation {V : Type*} [Fintype V] [DecidableEq V]
    (a : Quadratic V) (x : V → Bool) :
    (hamiltonian a).mulVec (basisState x) = (quadraticEval x a : ℂ) • basisState x := by
  rw [hamiltonian_diagonal]
  ext y
  rw [Matrix.mulVec_diagonal]
  by_cases h : y = x
  · subst y; simp [basisState]
  · simp [basisState,h]

/-- The basis vector of a Boolean configuration is a Hamiltonian eigenvector with eigenvalue
equal to its quadratic energy. -/
theorem basis_hasEigenvector {V : Type*} [Fintype V] [DecidableEq V]
    (a : Quadratic V) (x : V → Bool) :
    Module.End.HasEigenvector (hamiltonian a).toLin' (quadraticEval x a : ℂ) (basisState x) := by
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff]
  exact ⟨basis_eigen_equation a x,basisState_ne_zero x⟩

/-- A state vector is normalized when the sum of its squared complex norms is one. -/
def Normalized {V : Type*} [Fintype V] [DecidableEq V] (ψ : (V → Bool) → ℂ) : Prop :=
  ∑ x, Complex.normSq (ψ x) = 1

/-- The real part of the quadratic expectation of a matrix in a state vector. -/
def expectation {V : Type*} [Fintype V] [DecidableEq V]
    (H : Matrix (V → Bool) (V → Bool) ℂ) (ψ : (V → Bool) → ℂ) : ℝ :=
  (∑ x, star (ψ x) * (H.mulVec ψ) x).re

/-- The Hamiltonian expectation is the sum of classical quadratic energies weighted by the
squared norms of the state amplitudes. -/
theorem expectation_eq_weighted {V : Type*} [Fintype V] [DecidableEq V]
    (a : Quadratic V) (ψ : (V → Bool) → ℂ) :
    expectation (hamiltonian a) ψ = ∑ x, quadraticEval x a * Complex.normSq (ψ x) := by
  rw [expectation,hamiltonian_diagonal]
  simp_rw [Matrix.mulVec_diagonal]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_left_comm]
  change ((quadraticEval x a : ℂ) * ((starRingEnd ℂ) (ψ x) * ψ x)).re = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.ofReal_mul,Complex.ofReal_re]

/-- Every computational basis vector is normalized. -/
theorem basisState_normalized {V : Type*} [Fintype V] [DecidableEq V] (x : V → Bool) :
    Normalized (basisState x) := by simp [Normalized,basisState,Pi.single_apply]

/-- The Hamiltonian expectation in a basis vector equals the classical energy of its
configuration. -/
theorem expectation_basis {V : Type*} [Fintype V] [DecidableEq V]
    (a : Quadratic V) (x : V → Bool) :
    expectation (hamiltonian a) (basisState x) = quadraticEval x a := by
  rw [expectation_eq_weighted]
  simp [basisState,Pi.single_apply]

/-- A classical minimum of the quadratic energy bounds the Hamiltonian expectation from below in
every normalized state. -/
theorem quantum_ground_lower {V : Type*} [Fintype V] [DecidableEq V]
    (a : Quadratic V) (x : V → Bool)
    (hx : ∀ y, quadraticEval x a ≤ quadraticEval y a)
    (ψ : (V → Bool) → ℂ) (hψ : Normalized ψ) :
    quadraticEval x a ≤ expectation (hamiltonian a) ψ := by
  rw [expectation_eq_weighted]
  calc
    quadraticEval x a = ∑ y, quadraticEval x a * Complex.normSq (ψ y) := by
      rw [← Finset.mul_sum,hψ,mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun y _ =>
      mul_le_mul_of_nonneg_right (hx y) (Complex.normSq_nonneg _))

/-- A basis vector minimizes Hamiltonian expectation over normalized states exactly when its
configuration minimizes the classical quadratic energy; see [SuksmonoMinato2019]. -/
theorem basis_quantum_ground_iff {V : Type*} [Fintype V] [DecidableEq V]
    (a : Quadratic V) (x : V → Bool) :
    (∀ ψ, Normalized ψ → expectation (hamiltonian a) (basisState x) ≤
      expectation (hamiltonian a) ψ) ↔ ∀ y, quadraticEval x a ≤ quadraticEval y a := by
  constructor
  · intro h y
    have hy := h (basisState y) (basisState_normalized y)
    simpa only [expectation_basis] using hy
  · intro h ψ hψ
    rw [expectation_basis]
    exact quantum_ground_lower a x h ψ hψ

end Qatlib.Foundations.BooleanEnergy.QuboForms
