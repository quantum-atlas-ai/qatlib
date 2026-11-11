/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Ring

/-!
# Gram expansions for finite tensor registers

This module proves inner-product identities for complex amplitude functions on product
registers. The inner product of two simple tensors factors into the component inner products,
and the squared length of a finite tensor sum expands into products of the two component Gram
matrices.

The mathematical background is discussed in [NielsenChuang2010].

## Main statements

* `finite_tensor_inner`: factors the inner product of simple tensors.
* `finite_tensor_sum_gram`: expands the squared length of a finite sum of simple tensors.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.TensorRegisters.GramExpansion
open Matrix
open scoped BigOperators

/-- The Hermitian inner product of two simple tensor amplitude functions is the product of their
component inner products. -/
theorem finite_tensor_inner {I J : Type} [Fintype I] [Fintype J]
    (a a' : I → ℂ) (b b' : J → ℂ) :
    star (fun p : I × J => a p.1 * b p.2) ⬝ᵥ (fun p => a' p.1 * b' p.2) =
      (star a ⬝ᵥ a') * (star b ⬝ᵥ b') := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The squared length of a finite sum of simple tensors is the double sum of products of the
component Gram entries. -/
theorem finite_tensor_sum_gram {E I J : Type}
    [Fintype E] [Fintype I] [Fintype J]
    (a : E → I → ℂ) (b : E → J → ℂ) :
    star (∑ e, fun p : I × J => a e p.1 * b e p.2) ⬝ᵥ
        (∑ e, fun p : I × J => a e p.1 * b e p.2) =
      ∑ e, ∑ f, (star (a e) ⬝ᵥ a f) * (star (b e) ⬝ᵥ b f) := by
  calc
    _ = ∑ e, ∑ f,
        star (fun p : I × J => a e p.1 * b e p.2) ⬝ᵥ
          (fun p : I × J => a f p.1 * b f p.2) := by
      simp only [star_sum, sum_dotProduct, dotProduct_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [finite_tensor_inner]

end Qatlib.Foundations.TensorRegisters.GramExpansion
