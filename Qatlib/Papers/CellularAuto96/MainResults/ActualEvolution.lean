/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.OrderedKernel

/-!
# Scalar lattice evolution and its adjoint

This module defines the finite-neighborhood adjoint action and computes both evolution and
adjoint evolution on lattice basis states. A right-inverse identity for the adjoint implies the
weight unitarity condition and yields the integer-lattice translation conclusion associated with
[Meyer1996].

## Main statements

* `unitary_of_adjoint_inverse`: derives weight unitarity from the evolution identity.
* `noGo_actual_integer_lattice`: reduces the evolution to one translation with a unit-modulus
  coefficient.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.QcaDynamics.ScalarNoGo
namespace Qatlib.Papers.CellularAuto96.MainResults

/-- The finite-neighborhood adjoint action, summing conjugated weights against the state at
displacements `x - e`. -/
def adjointStep {V : Type*} [Sub V] (A : Weights V) (φ : V → ℂ) : V → ℂ :=
  fun x => ∑ e ∈ A.neighborhood, star (A.weight e) * φ (x - e)

/-- The lattice basis function equal to one at `y` and zero elsewhere. -/
def latticeKet {V : Type*} [DecidableEq V] (y : V) : V → ℂ :=
  fun x => if x = y then 1 else 0

/-- Evolution of the lattice basis state at `y`, evaluated at `x`, equals the displacement
weight `A.weight (y - x)`. -/
theorem step_ket {V : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Weights V) (y x : V) : step A (latticeKet y) x = A.weight (y - x) := by
  unfold step latticeKet
  have heq : ∀ e : V, x + e = y ↔ e = y - x := by
    intro e
    constructor
    · intro h
      have h' := congrArg (fun z => z - x) h
      simpa using h'
    · intro h
      rw [h]
      abel
  simp_rw [heq]
  rw [Finset.sum_eq_single (y - x)]
  · simp
  · intro e _ he
    simp [he]
  · intro he
    have hz : A.weight (y - x) = 0 := by
      by_contra h
      exact he (A.support _ h)
    simp [hz]

/-- The adjoint action on the basis state at `y`, evaluated at `x`, is the conjugate of the
forward transition from `x` to `y`, matching the scalar evolution convention in [Meyer1996]. -/
theorem adjointStep_ket {V : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Weights V) (y x : V) :
    adjointStep A (latticeKet y) x = star (step A (latticeKet x) y) := by
  rw [step_ket]
  unfold adjointStep latticeKet
  have heq : ∀ e : V, x - e = y ↔ e = x - y := by
    intro e
    constructor
    · intro h
      have h' : x - y = e := by rw [← h]; abel
      exact h'.symm
    · intro h
      rw [h]
      abel
  simp_rw [heq]
  rw [Finset.sum_eq_single (x - y)]
  · simp
  · intro e _ he
    simp [he]
  · intro he
    have hz : A.weight (x - y) = 0 := by
      by_contra h
      exact he (A.support _ h)
    simp [hz]

/-- Forward evolution after adjoint evolution of the origin basis state gives the finite weight
autocorrelation sum at displacement `d`. -/
theorem step_adjoint_origin {V : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Weights V) (d : V) :
    step A (adjointStep A (latticeKet 0)) d =
      ∑ e ∈ A.neighborhood, A.weight e * star (A.weight (e + d)) := by
  unfold step adjointStep latticeKet
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have heq : ∀ f : V, d + e - f = 0 ↔ f = e + d := by
    intro f
    rw [sub_eq_zero, eq_comm, add_comm d e]
  simp_rw [heq]
  rw [Finset.sum_eq_single (e + d)]
  · simp
  · intro f _ hf
    simp [hf]
  · intro hf
    have hz : A.weight (e + d) = 0 := by
      by_contra h
      exact hf (A.support _ h)
    simp [hz]

/-- If forward evolution composed with the adjoint action is the identity on all state
functions, the weights satisfy `Unitary`. -/
theorem unitary_of_adjoint_inverse {V : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Weights V) (hU : ∀ φ : V → ℂ, step A (adjointStep A φ) = φ) : Unitary A := by
  constructor
  · have h := congrFun (hU (latticeKet 0)) 0
    simpa [step_adjoint_origin, latticeKet] using h
  · intro d hd
    have h := congrFun (hU (latticeKet 0)) (-d)
    simpa [step_adjoint_origin, latticeKet, hd, sub_eq_add_neg] using h

/-- On the integer lattice, a right-inverse identity for the adjoint action forces exactly one
nonzero displacement weight of modulus one and the corresponding translation evolution. This
realizes the scalar lattice no-go conclusion associated with [Meyer1996]. -/
theorem noGo_actual_integer_lattice (d : ℕ) (A : Weights (Fin d → ℤ))
    (hU : ∀ φ : (Fin d → ℤ) → ℂ, step A (adjointStep A φ) = φ) :
    ∃ (e₀ : Fin d → ℤ) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      (∀ e, A.weight e ≠ 0 → e = e₀) ∧ evolveByTranslation A e₀ c := by
  exact noGo_finDimension d A (unitary_of_adjoint_inverse A hU)

/-- Finite-neighborhood evolution packaged as a complex linear map on lattice state functions. -/
def stepLinear {V : Type*} [Add V] (A : Weights V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun := step A
  map_add' φ ψ := by
    funext x
    simp [step, mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext x
    simp [step, Finset.mul_sum, mul_left_comm, smul_eq_mul]

end Qatlib.Papers.CellularAuto96.MainResults
