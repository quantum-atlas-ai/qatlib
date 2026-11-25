/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.OperatorErrors.OperatorError

@[expose] public section

/-!
# Unitary product error bridges

The public operator-error toolkit already proves the finite telescoping estimate in the Euclidean
operator norm.  This module gives that result a query-execution-facing name and adds the two
consumer forms used most often by algorithm papers: a uniform per-call error bound and the induced
state-vector distance bound on `EuclideanSpace ℂ I`.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Foundations.QueryExecution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The product of two equally indexed unitary families differs by at most the sum of the
pointwise Euclidean operator-norm errors. -/
theorem unitary_product_error {n : ℕ} (A B : Fin n → Matrix I I ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup I ℂ)
    (hB : ∀ i, B i ∈ Matrix.unitaryGroup I ℂ) :
    ‖(List.ofFn A).prod - (List.ofFn B).prod‖ ≤ ∑ i, ‖A i - B i‖ := by
  apply Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_prod_sub_prod_le A B
  · intro i
    exact Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one (hA i)
  · intro i
    exact Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one (hB i)

/-- A uniform per-call approximation error accumulates linearly over a unitary product. -/
theorem unitary_product_error_of_uniform {n : ℕ} (A B : Fin n → Matrix I I ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup I ℂ)
    (hB : ∀ i, B i ∈ Matrix.unitaryGroup I ℂ) (ε : ℝ)
    (hε : ∀ i, ‖A i - B i‖ ≤ ε) :
    ‖(List.ofFn A).prod - (List.ofFn B).prod‖ ≤ (n : ℝ) * ε := by
  refine (unitary_product_error A B hA hB).trans ?_
  calc
    ∑ i, ‖A i - B i‖ ≤ ∑ _i : Fin n, ε :=
      Finset.sum_le_sum fun i _ => hε i
    _ = (n : ℝ) * ε := by simp [nsmul_eq_mul]

/-- The product-operator estimate transports directly to normalized or unnormalized Euclidean
state vectors through the induced matrix action. -/
theorem unitary_product_state_error {n : ℕ} (A B : Fin n → Matrix I I ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup I ℂ)
    (hB : ∀ i, B i ∈ Matrix.unitaryGroup I ℂ) (ψ : EuclideanSpace ℂ I) :
    ‖(EuclideanSpace.equiv I ℂ).symm
        (((List.ofFn A).prod - (List.ofFn B).prod) *ᵥ ψ.ofLp)‖ ≤
      (∑ i, ‖A i - B i‖) * ‖ψ‖ := by
  have hmul := Matrix.l2_opNorm_mulVec
    ((List.ofFn A).prod - (List.ofFn B).prod) ψ
  have hprod := unitary_product_error A B hA hB
  exact hmul.trans (mul_le_mul_of_nonneg_right hprod (norm_nonneg ψ))

end Qatlib.Foundations.QueryExecution
