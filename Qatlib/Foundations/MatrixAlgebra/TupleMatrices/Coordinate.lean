/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TupleMatrices.FiniteProduct

/-!
# Coordinate actions on product amplitudes

The module factors a product amplitude at one coordinate and tracks how that factor changes
under a coordinate update. `coordinate_intertwines` lifts the single-register identity `G * C =
C * diagonal phase` to the action on a selected coordinate of a product amplitude.

These identities express the coordinatewise matrix algebra underlying tensor-product quantum
registers [NielsenChuang2010].

## Main statements

* `product_update`: isolate the updated coordinate in a finite product.
* `coordinate_intertwines`: transport a single-register diagonal intertwining identity to
  product coordinates.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.TupleMatrices
variable {X A B : Type*} [Fintype X]

/-- Updating one coordinate of the row tuple replaces the corresponding matrix factor and leaves
the product over all other coordinates unchanged. -/
theorem product_update (C : Matrix B A ℂ) (db : X → B) (f : X → A) (x : X) (value : B) :
    (∏ j,C (Function.update db x value j) (f j))=
      C value (f x)*∏ j ∈ (Finset.univ : Finset X) \ {x},C (db j) (f j) := by
  have h : (fun j => C (Function.update db x value j) (f j))=
      Function.update (fun j => C (db j) (f j)) x (C value (f x)) := by
    funext j
    by_cases hj : j=x
    · subst j
      rw [Function.update_self,Function.update_self]
    · rw [Function.update_of_ne hj,Function.update_of_ne hj]
  rw [h,Finset.prod_update_of_mem (Finset.mem_univ x)]

/-- A product of matrix entries factors as the selected coordinate entry times the product over
the remaining coordinates. -/
theorem product_coordinate (C : Matrix B A ℂ) (db : X → B) (f : X → A) (x : X) :
    (∏ j,C (db j) (f j))=C (db x) (f x)*∏ j ∈ (Finset.univ : Finset X) \ {x},C (db j) (f j) := by
  simpa only [Function.update_eq_self] using product_update C db f x (db x)

/-- If `G * C = C * diagonal phase`, applying `G` at one coordinate of a product amplitude
multiplies that amplitude by the corresponding phase. -/
theorem coordinate_intertwines [Fintype A] [Fintype B] (C : Matrix B A ℂ) (G : Matrix B B ℂ)
    (phase : A → ℂ) (hGC : G*C=C*diagonal phase)
    (db : X → B) (f : X → A) (x : X) :
    (∑ value : B,G (db x) value*(∏ j,C (Function.update db x value j) (f j)))=
      (∏ j,C (db j) (f j))*phase (f x) := by
  simp_rw [product_update C db f x]
  have hentry := congrArg (fun M : Matrix B A ℂ => M (db x) (f x)) hGC
  try dsimp only at hentry
  rw [Matrix.mul_diagonal] at hentry
  change (∑ value : B,G (db x) value*C value (f x))=C (db x) (f x)*phase (f x) at hentry
  calc
    _ = (∑ value : B,G (db x) value*C value (f x))*
        ∏ j ∈ (Finset.univ : Finset X) \ {x},C (db j) (f j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro value hvalue
      ring
    _ = _ := by rw [hentry,product_coordinate C db f x];ring
end Qatlib.Foundations.MatrixAlgebra.TupleMatrices
