/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Qatlib.Foundations.TensorRegisters.GramExpansion
open Matrix
open scoped BigOperators

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
