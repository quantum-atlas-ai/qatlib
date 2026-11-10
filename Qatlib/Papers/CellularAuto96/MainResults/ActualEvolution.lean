/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.OrderedKernel

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.QcaDynamics.ScalarNoGo
namespace Qatlib.Papers.CellularAuto96.MainResults

def adjointStep {V : Type*} [Sub V] (A : Weights V) (φ : V → ℂ) : V → ℂ :=
  fun x => ∑ e ∈ A.neighborhood, star (A.weight e) * φ (x - e)

def latticeKet {V : Type*} [DecidableEq V] (y : V) : V → ℂ :=
  fun x => if x = y then 1 else 0

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

theorem unitary_of_adjoint_inverse {V : Type*} [AddCommGroup V] [DecidableEq V]
    (A : Weights V) (hU : ∀ φ : V → ℂ, step A (adjointStep A φ) = φ) : Unitary A := by
  constructor
  · have h := congrFun (hU (latticeKet 0)) 0
    simpa [step_adjoint_origin, latticeKet] using h
  · intro d hd
    have h := congrFun (hU (latticeKet 0)) (-d)
    simpa [step_adjoint_origin, latticeKet, hd, sub_eq_add_neg] using h

theorem noGo_actual_integer_lattice (d : ℕ) (A : Weights (Fin d → ℤ))
    (hU : ∀ φ : (Fin d → ℤ) → ℂ, step A (adjointStep A φ) = φ) :
    ∃ (e₀ : Fin d → ℤ) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      (∀ e, A.weight e ≠ 0 → e = e₀) ∧ evolveByTranslation A e₀ c := by
  exact noGo_finDimension d A (unitary_of_adjoint_inverse A hU)

def stepLinear {V : Type*} [Add V] (A : Weights V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun := step A
  map_add' φ ψ := by
    funext x
    simp [step, mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext x
    simp [step, Finset.mul_sum, mul_left_comm, smul_eq_mul]

end Qatlib.Papers.CellularAuto96.MainResults
