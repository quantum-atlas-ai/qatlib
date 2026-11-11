/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Partial swap and the finite matrix trace identity

Defines a partial trace over `C`, the permutation `swapEquiv` exchanging the two `I`
coordinates, and its matrix `swapOp`. The theorem `swap_trick` identifies the trace against the
two-copy matrix `kron ρ` with the trace of the square of `partialTrace ρ`. See
[CotlerGongKannan2025] for the surrounding analysis.

## Main statements

* `swapEquiv`: The permutation exchanging the two `I` coordinates and retaining each `C`
  coordinate in place.
* `swap_trick`: For any matrix `ρ`, the trace of `swapOp * kron ρ` equals the trace of
  `partialTrace ρ * partialTrace ρ`.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.SwapTrick

open Matrix
open scoped BigOperators

variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]

/-- The partial trace of a matrix over the `C` coordinate, with entries `∑ c, ρ (i, c) (j, c)`. -/
def partialTrace (ρ : Matrix (I × C) (I × C) ℂ) : Matrix I I ℂ :=
  fun i j => ∑ c : C, ρ (i, c) (j, c)

/-- The permutation exchanging the two `I` coordinates and retaining each `C` coordinate in
place. -/
def swapEquiv : ((I × C) × (I × C)) ≃ ((I × C) × (I × C)) where
  toFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  left_inv := by rintro ⟨⟨i1, c1⟩, ⟨i2, c2⟩⟩; rfl
  right_inv := by rintro ⟨⟨i1, c1⟩, ⟨i2, c2⟩⟩; rfl

/-- Applying the partial-swap permutation twice returns the original pair. -/
@[simp] theorem swapEquiv_swapEquiv (x : (I × C) × (I × C)) :
    swapEquiv (swapEquiv x) = x := by
  rcases x with ⟨⟨i1, c1⟩, ⟨i2, c2⟩⟩
  rfl

/-- The permutation matrix implementing `swapEquiv`. -/
def swapOp : Matrix ((I × C) × (I × C)) ((I × C) × (I × C)) ℂ :=
  fun x y => if x = swapEquiv y then 1 else 0

/-- The two-copy tensor-product matrix with entries `ρ x.1 y.1 * ρ x.2 y.2`. -/
def kron (ρ : Matrix (I × C) (I × C) ℂ) :
    Matrix ((I × C) × (I × C)) ((I × C) × (I × C)) ℂ :=
  fun x y => ρ x.1 y.1 * ρ x.2 y.2

/-- The first output pair of `swapEquiv ((i1, c1), (i2, c2))` is `(i2, c1)`. -/
theorem swapEquiv_fst (i1 i2 : I) (c1 c2 : C) :
    (swapEquiv ((i1, c1), (i2, c2))).1 = (i2, c1) := rfl

/-- The second output pair of `swapEquiv ((i1, c1), (i2, c2))` is `(i1, c2)`. -/
theorem swapEquiv_snd (i1 i2 : I) (c1 c2 : C) :
    (swapEquiv ((i1, c1), (i2, c2))).2 = (i1, c2) := rfl

/-- For any matrix `ρ`, the trace of `swapOp * kron ρ` equals the trace of `partialTrace ρ *
partialTrace ρ` [CotlerGongKannan2025]. -/
theorem swap_trick (ρ : Matrix (I × C) (I × C) ℂ) :
    Matrix.trace (swapOp (I := I) (C := C) * kron ρ) =
      Matrix.trace (partialTrace ρ * partialTrace ρ) := by

  have hcoll : ∀ x : (I × C) × (I × C),
      (∑ y, (if x = swapEquiv y then (1 : ℂ) else 0) * (ρ y.1 x.1 * ρ y.2 x.2))
        = ρ (swapEquiv x).1 x.1 * ρ (swapEquiv x).2 x.2 := by
    intro x
    rw [Finset.sum_eq_single (swapEquiv x)]
    · simp
    · intro y _ hy
      have hne : x ≠ swapEquiv y := by
        intro h
        apply hy
        rw [h, swapEquiv_swapEquiv]
      simp [hne]
    · intro hx
      exact absurd (Finset.mem_univ _) hx
  have hL : Matrix.trace (swapOp (I := I) (C := C) * kron ρ) =
      ∑ i : I, ∑ c1 : C, ∑ j : I, ∑ c2 : C,
        ρ (i, c1) (j, c1) * ρ (j, c2) (i, c2) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, swapOp, kron]
    simp only [hcoll]
    rw [Fintype.sum_equiv swapEquiv
      (fun x : (I × C) × (I × C) => ρ (swapEquiv x).1 x.1 * ρ (swapEquiv x).2 x.2)
      (fun y : (I × C) × (I × C) => ρ y.1 (swapEquiv y).1 * ρ y.2 (swapEquiv y).2)
      (fun x => by simp)]
    simp only [Fintype.sum_prod_type, swapEquiv_fst, swapEquiv_snd]
  have hR : Matrix.trace (partialTrace ρ * partialTrace ρ) =
      ∑ i : I, ∑ c1 : C, ∑ j : I, ∑ c2 : C,
        ρ (i, c1) (j, c1) * ρ (j, c2) (i, c2) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, partialTrace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hpt : ∀ j : I, (∑ c : C, ρ (i, c) (j, c)) * (∑ c : C, ρ (j, c) (i, c))
        = ∑ c1 : C, ∑ c2 : C, ρ (i, c1) (j, c1) * ρ (j, c2) (i, c2) :=
      fun j => Fintype.sum_mul_sum (fun c => ρ (i, c) (j, c)) (fun c => ρ (j, c) (i, c))
    simp only [hpt]
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j c1 => ∑ c2 : C, ρ (i, c1) (j, c1) * ρ (j, c2) (i, c2))
  rw [hL, hR]

end Qatlib.Papers.NoisyLearn26.MainResults.SwapTrick
