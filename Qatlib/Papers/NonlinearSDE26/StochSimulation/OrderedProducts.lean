/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.OperatorErrors.OperatorError
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Telescoping the ordered products in Proposition 34

Equation (217) of arXiv:2603.12398v1 bounds products of short-time
operators with a common norm bound. Operator products are in
application order, with the factor of time step zero on the right.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.NonlinearSDE26.StochSimulation

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The matrix product with the earliest factor on the right. -/
def orderedFactorProduct {k : ℕ} (A : Fin k → Matrix I I ℂ) : Matrix I I ℂ :=
  (List.ofFn A).reverse.prod

/-- Removing the earliest factor leaves the tail product on its left. -/
private theorem orderedFactorProduct_succ {k : ℕ} (A : Fin (k + 1) → Matrix I I ℂ) :
    orderedFactorProduct A = orderedFactorProduct (fun j => A j.succ) * A 0 := by
  simp only [orderedFactorProduct, List.ofFn_succ, List.reverse_cons, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]

/-- A product of positive length has norm at most the common bound to that power. -/
private theorem orderedFactorProduct_norm_le {k : ℕ} (A : Fin (k + 1) → Matrix I I ℂ)
    (Λ : ℝ) (hA : ∀ j, ‖A j‖ ≤ Λ) : ‖orderedFactorProduct A‖ ≤ Λ ^ (k + 1) := by
  induction k with
  | zero => simpa [orderedFactorProduct, List.ofFn_succ] using hA 0
  | succ k ih =>
    have hΛ := (norm_nonneg _).trans (hA 0)
    rw [orderedFactorProduct_succ, pow_succ]
    exact (norm_mul_le _ _).trans
      (mul_le_mul (ih (fun j => A j.succ) (fun j => hA j.succ)) (hA 0)
        (norm_nonneg _) (pow_nonneg hΛ _))

/-- Proposition 34, Eq. (217), for Euclidean operator norm and in the
source's multiplication order. The length-zero products agree. -/
theorem prop34_prod_sub_prod_le {k : ℕ} (A B : Fin k → Matrix I I ℂ)
    (Λ : ℝ) (hA : ∀ j, ‖A j‖ ≤ Λ) (hB : ∀ j, ‖B j‖ ≤ Λ) :
    ‖orderedFactorProduct A - orderedFactorProduct B‖ ≤
      Λ ^ (k - 1) * ∑ j, ‖A j - B j‖ := by
  induction k with
  | zero => simp [orderedFactorProduct]
  | succ k ih =>
    cases k with
    | zero => simp [orderedFactorProduct, List.ofFn_succ]
    | succ k =>
      let A' : Fin (k + 1) → Matrix I I ℂ := fun j => A j.succ
      let B' : Fin (k + 1) → Matrix I I ℂ := fun j => B j.succ
      have hΛ := (norm_nonneg _).trans (hA 0)
      have hsplit :
          orderedFactorProduct A - orderedFactorProduct B =
            orderedFactorProduct A' * (A 0 - B 0) +
              (orderedFactorProduct A' - orderedFactorProduct B') * B 0 := by
        rw [orderedFactorProduct_succ A, orderedFactorProduct_succ B]
        change orderedFactorProduct A' * A 0 - orderedFactorProduct B' * B 0 = _
        noncomm_ring
      rw [hsplit, Fin.sum_univ_succ]
      change _ ≤ Λ ^ (k + 1) * (‖A 0 - B 0‖ + ∑ j, ‖A' j - B' j‖)
      have htail := ih A' B' (fun j => hA j.succ) (fun j => hB j.succ)
      calc
        _ ≤ ‖orderedFactorProduct A'‖ * ‖A 0 - B 0‖ +
            ‖orderedFactorProduct A' - orderedFactorProduct B'‖ * ‖B 0‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ Λ ^ (k + 1) * ‖A 0 - B 0‖ + (Λ ^ k * ∑ j, ‖A' j - B' j‖) * Λ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (orderedFactorProduct_norm_le A' Λ
              (fun j => hA j.succ)) (norm_nonneg _))
            (mul_le_mul htail (hB 0) (norm_nonneg _)
              (mul_nonneg (pow_nonneg hΛ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
        _ = _ := by rw [pow_succ]; ring

end Qatlib.Papers.NonlinearSDE26.StochSimulation
