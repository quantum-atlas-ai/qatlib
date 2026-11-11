/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Spatial operators on a spin register

This module models the spatial-only action underlying spin-free simulation in [Whitfield2013].
The matrix `liftSpatial A` acts as `A` on the spatial index and as the identity on the spin
index, and `productState` fixes a chosen spin label.

## Main statements

* `liftSpatial_mul` and `liftSpatial_conjTranspose`: compatibility with multiplication and
  adjoints.
* `liftSpatial_unitary`: preservation of the two unitary identities.
* `spinFree_simulation`: unitary spatial evolution of the spatial component of a product state.

## References

* [Whitfield, 2013][Whitfield2013]
-/

set_option autoImplicit false

namespace Qatlib.Papers.SpinFreeSim13.ConditionalLift

open Matrix

variable {R S : Type*}

/-- Lifts a spatial matrix to the product register by tensoring its entries with the identity on
the spin index. -/
def liftSpatial [DecidableEq S] (A : Matrix R R ℂ) : Matrix (R × S) (R × S) ℂ :=
  fun a b => A a.1 b.1 * (if a.2 = b.2 then (1 : ℂ) else 0)

/-- The spatial lift of the identity matrix is the identity on the product register. -/
theorem liftSpatial_one [DecidableEq R] [DecidableEq S] :
    liftSpatial (R := R) (S := S) (1 : Matrix R R ℂ) = 1 := by
  ext a b
  simp only [liftSpatial, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · by_cases h1 : a.1 = b.1
    · have h2 : a.2 ≠ b.2 := fun h2 => h (Prod.ext h1 h2)
      simp [h, h1, h2]
    · simp [h, h1]

/-- Summing a product of two complex Kronecker deltas over the intermediate index gives the
delta between the exterior indices. -/
theorem sum_ite_delta {S : Type*} [Fintype S] [DecidableEq S] (x z : S) :
    (∑ y : S, (if x = y then (1 : ℂ) else 0) * (if y = z then (1 : ℂ) else 0))
      = (if x = z then 1 else 0) := by
  classical
  by_cases h : x = z
  · subst h
    rw [Finset.sum_eq_single x] <;> simp_all
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x = y
    · subst hxy; simp [h]
    · simp [hxy]

/-- The spatial lift preserves matrix multiplication. -/
theorem liftSpatial_mul [Fintype R] [Fintype S] [DecidableEq S] (A B : Matrix R R ℂ) :
    liftSpatial (R := R) (S := S) (A * B) = liftSpatial A * liftSpatial B := by
  ext a b
  simp only [liftSpatial, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : R, A a.1 j * B j b.1) * (if a.2 = b.2 then (1 : ℂ) else 0)
        = ∑ x : R, (A a.1 x * B x b.1) * (if a.2 = b.2 then (1 : ℂ) else 0) := by
          rw [Finset.sum_mul]
    _ = ∑ x : R, (A a.1 x * B x b.1) *
            (∑ y : S, (if a.2 = y then (1 : ℂ) else 0) * (if y = b.2 then (1 : ℂ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← sum_ite_delta]
    _ = ∑ x : R, ∑ y : S,
        (A a.1 x * (if a.2 = y then (1 : ℂ) else 0)) *
          (B x b.1 * (if y = b.2 then (1 : ℂ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring

/-- The spatial lift commutes with conjugate transpose. -/
theorem liftSpatial_conjTranspose [Fintype R] [Fintype S] [DecidableEq S] (A : Matrix R R ℂ) :
    liftSpatial (R := R) (S := S) A.conjTranspose = (liftSpatial A).conjTranspose := by
  ext a b
  simp only [liftSpatial, Matrix.conjTranspose_apply, star_mul]
  by_cases h : a.2 = b.2
  · rw [if_pos h, if_pos h.symm]; simp
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]; simp

/-- The product amplitude with spatial component `ψ` and spin component supported at `s0`. -/
def productState [DecidableEq S] (ψ : R → ℂ) (s0 : S) : R × S → ℂ :=
  fun a => ψ a.1 * (if a.2 = s0 then (1 : ℂ) else 0)

/-- A lifted spatial matrix acts on the spatial component of a product state and preserves its
fixed spin component. -/
theorem liftSpatial_mulVec_productState [Fintype R] [Fintype S] [DecidableEq S]
    (U : Matrix R R ℂ) (ψ : R → ℂ) (s0 : S) :
    liftSpatial U *ᵥ productState ψ s0 = productState (U *ᵥ ψ) s0 := by
  ext a
  simp only [liftSpatial, productState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  calc
    ∑ x : R, ∑ y : S,
        (U a.1 x * (if a.2 = y then (1 : ℂ) else 0)) *
          (ψ x * (if y = s0 then (1 : ℂ) else 0))
        = ∑ x : R, (U a.1 x * ψ x) *
            (∑ y : S, (if a.2 = y then (1 : ℂ) else 0) * (if y = s0 then (1 : ℂ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ x : R, (U a.1 x * ψ x) * (if a.2 = s0 then (1 : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [sum_ite_delta]
    _ = (∑ x : R, U a.1 x * ψ x) * (if a.2 = s0 then (1 : ℂ) else 0) := by
          rw [Finset.sum_mul]

/-- If a spatial matrix satisfies both unitary identities, its spatial lift satisfies both
identities on the product register. -/
theorem liftSpatial_unitary [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (U : Matrix R R ℂ)
    (hU : U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1) :
    (liftSpatial (R := R) (S := S) U).conjTranspose * liftSpatial U = 1 ∧
      liftSpatial U * (liftSpatial (R := R) (S := S) U).conjTranspose = 1 := by
  constructor
  · rw [← liftSpatial_conjTranspose, ← liftSpatial_mul, hU.1, liftSpatial_one]
  · rw [← liftSpatial_conjTranspose, ← liftSpatial_mul, hU.2, liftSpatial_one]

/-- The spatial lift is injective when the spin index type is nonempty. -/
theorem liftSpatial_injective [DecidableEq S] [Nonempty S] :
    Function.Injective (liftSpatial : Matrix R R ℂ → Matrix (R × S) (R × S) ℂ) := by
  intro A B h
  ext r r'
  have h' := congrFun (congrFun h (r, Classical.arbitrary S)) (r', Classical.arbitrary S)
  simpa [liftSpatial] using h'

/-- A unitary spatial matrix lifts to a unitary matrix on the product register and acts on a
product state by evolving only its spatial component. See [Whitfield2013]. -/
theorem spinFree_simulation [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (U : Matrix R R ℂ)
    (hU : U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1)
    (ψ : R → ℂ) (s0 : S) :
    (liftSpatial (R := R) (S := S) U).conjTranspose * liftSpatial U = 1 ∧
      liftSpatial U * (liftSpatial (R := R) (S := S) U).conjTranspose = 1 ∧
      liftSpatial U *ᵥ productState ψ s0 = productState (U *ᵥ ψ) s0 :=
  ⟨(liftSpatial_unitary U hU).1, (liftSpatial_unitary U hU).2,
    liftSpatial_mulVec_productState U ψ s0⟩

end Qatlib.Papers.SpinFreeSim13.ConditionalLift
