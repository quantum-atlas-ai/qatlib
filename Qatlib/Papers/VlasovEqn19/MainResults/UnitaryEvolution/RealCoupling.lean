/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VlasovEqn19.MainResults.UnitaryEvolution.SourceUnitaryEvolution

@[expose] public section

/-!
# Real velocity–field couplings

The real coefficients couple the two blocks in both directions in
arXiv:1907.09418. In the one-dimensional reduction, combine the coupling
to the distinguished electric field with the diagonal streaming term in
Eq. (18). Its rows are the generator of Eqs. (15)–(16).
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Papers.VlasovEqn19.MainResults.UnitaryEvolution (propagator propagator_unitary)

namespace Qatlib.Papers.VlasovEqn19.MainResults.UnitaryEvolution

/-- A rectangular real coupling and its transpose in the two off-diagonal blocks. -/
def realCoupling {V E : Type*} (c : V → E → ℝ) : Matrix (V ⊕ E) (V ⊕ E) ℂ :=
  Matrix.of fun a b => match a, b with
    | .inl j, .inr e => (c j e : ℂ)
    | .inr e, .inl j => (c j e : ℂ)
    | _, _ => 0

/-- A real coupling placed in both directions is Hermitian. -/
theorem coupling_isHermitian {V E : Type*} (c : V → E → ℝ) :
    (realCoupling c).IsHermitian := by
  apply Matrix.ext
  intro a b
  cases a <;> cases b <;> simp [realCoupling, Matrix.conjTranspose_apply]

/-- The coupling entry in the velocity row is the sum of field inputs with the row's coefficients. -/
theorem coupling_velocity_row {V E : Type*} [Fintype V] [Fintype E]
    (c : V → E → ℝ) (x : V ⊕ E → ℂ) (j : V) :
    (realCoupling c *ᵥ x) (.inl j) = ∑ e, (c j e : ℂ) * x (.inr e) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, realCoupling]

/-- The field row is the transposed coupling applied to the velocity inputs. -/
theorem coupling_field_row {V E : Type*} [Fintype V] [Fintype E]
    (c : V → E → ℝ) (x : V ⊕ E → ℂ) (e : E) :
    (realCoupling c *ᵥ x) (.inr e) = ∑ j, (c j e : ℂ) * x (.inl j) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, realCoupling]

/-- The exact one-dimensional Hamiltonian of Eq. (18) on velocity modes and one field mode. -/
def oneDimensionalHamiltonian {V : Type*} [DecidableEq V] (k : ℝ) (v α : V → ℝ) :
    Matrix (V ⊕ Unit) (V ⊕ Unit) ℂ :=
  Matrix.diagonal (fun s => match s with
    | .inl j => ((k * v j : ℝ) : ℂ)
    | .inr _ => 0) + realCoupling (fun j _ => α j * v j)

/-- Both the streaming diagonal and the real coupling in Eq. (18) are Hermitian. -/
theorem oneDimensionalHamiltonian_isHermitian {V : Type*} [DecidableEq V]
    (k : ℝ) (v α : V → ℝ) : (oneDimensionalHamiltonian k v α).IsHermitian := by
  apply Matrix.IsHermitian.add
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro s
    cases s <;> simp [isSelfAdjoint_iff]
  · exact coupling_isHermitian (fun j _ => α j * v j)

/-- The velocity row of Eq. (18), before the common factor `-i` in Eq. (15). -/
theorem oneDimensional_velocity_row {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℝ) (v α : V → ℝ) (x : V ⊕ Unit → ℂ) (j : V) :
    (oneDimensionalHamiltonian k v α *ᵥ x) (.inl j) =
      ((k * v j : ℝ) : ℂ) * x (.inl j) + ((α j * v j : ℝ) : ℂ) * x (.inr ()) := by
  rw [oneDimensionalHamiltonian, Matrix.add_mulVec]
  simp [Matrix.mulVec_diagonal, coupling_velocity_row]

/-- The electric-field row of Eq. (18), before the common factor `-i` in Eq. (16). -/
theorem oneDimensional_field_row {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℝ) (v α : V → ℝ) (x : V ⊕ Unit → ℂ) :
    (oneDimensionalHamiltonian k v α *ᵥ x) (.inr ()) =
      ∑ j, ((α j * v j : ℝ) : ℂ) * x (.inl j) := by
  rw [oneDimensionalHamiltonian, Matrix.add_mulVec]
  simp [Matrix.mulVec_diagonal, coupling_field_row]

/-- The exact finite one-dimensional Hamiltonian generates unitary forward evolution
with the `-i H t` sign used in the source. -/
theorem oneDimensional_evolution_unitary {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℝ) (v α : V → ℝ) (t : ℝ) :
    let U := NormedSpace.exp ((-(t : ℂ) * Complex.I) • oneDimensionalHamiltonian k v α)
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  simpa [propagator] using
    propagator_unitary (oneDimensionalHamiltonian k v α)
      (oneDimensionalHamiltonian_isHermitian k v α) (-t)

end Qatlib.Papers.VlasovEqn19.MainResults.UnitaryEvolution
