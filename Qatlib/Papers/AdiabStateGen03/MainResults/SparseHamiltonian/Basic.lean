/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Norm estimates for Hamiltonian simulation

This module proves basic error estimates for sums and ordered products used in sparse
Hamiltonian simulation. In particular, `list_prod_sub_prod_le` bounds product error by the sum
of factor errors for lists of contractions, and `timeEvolution_zero` identifies evolution at
time zero. The mathematical context is [AharonovTaShma2007].

## Main statements

* `norm_sum_sub_sum_le`: Uniform error at most `ε` for each term of a finite operator sum gives
  total error at most the number of terms times `ε`.
* `list_prod_sub_prod_le`: For equal-length lists of contractions, the norm of the difference of
  their ordered products is bounded by the sum of the norms of corresponding factor differences.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

/-- The time-evolution operator at time zero is the identity for every Hamiltonian
[AharonovTaShma2007]. -/
theorem timeEvolution_zero (H : Ham n) : timeEvolution H 0 = 1 := by
  unfold timeEvolution
  have h : (-(0 : ℝ)) • (Complex.I • toOp H) = 0 := by
    ext v
    simp
  rw [h, NormedSpace.exp_zero]

/-- Uniform error at most `ε` for each term of a finite operator sum gives total error at most
the number of terms times `ε` [AharonovTaShma2007]. -/
theorem norm_sum_sub_sum_le {ι : Type*} [Fintype ι] (f g : ι → Op n) (ε : ℝ)
    (h : ∀ i, ‖f i - g i‖ ≤ ε) :
    ‖∑ i, f i - ∑ i, g i‖ ≤ (Fintype.card ι : ℝ) * ε := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ i, (f i - g i)‖ ≤ ∑ i, ‖f i - g i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum (fun i _ => h i)
    _ = (Fintype.card ι : ℝ) * ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A finite ordered product of elements of norm at most one has norm at most one
[AharonovTaShma2007]. -/
lemma norm_list_prod_le_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    {l : List R} (h : ∀ a ∈ l, ‖a‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons a as ih =>
      rw [List.prod_cons]
      calc ‖a * as.prod‖ ≤ ‖a‖ * ‖as.prod‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by
            gcongr
            · exact h a (by simp)
            · exact ih (fun x hx => h x (by simp [hx]))
        _ = 1 := by ring

/-- For equal-length lists of contractions, the norm of the difference of their ordered products
is bounded by the sum of the norms of corresponding factor differences [AharonovTaShma2007]. -/
theorem list_prod_sub_prod_le {R : Type*} [SeminormedRing R] [NormOneClass R]
    (l₁ : List R) :
    ∀ (l₂ : List R), l₁.length = l₂.length →
      (∀ a ∈ l₁, ‖a‖ ≤ 1) → (∀ a ∈ l₂, ‖a‖ ≤ 1) →
      ‖l₁.prod - l₂.prod‖ ≤ (l₁.zipWith (fun a b => ‖a - b‖) l₂).sum := by
  induction l₁ with
  | nil =>
      intro l₂ hlen _ _
      cases l₂ with
      | nil => simp
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro l₂ hlen h1 h2
      cases l₂ with
      | nil => simp at hlen
      | cons b bs =>
          rw [List.prod_cons, List.prod_cons, List.zipWith_cons_cons, List.sum_cons]
          have hlen' : as.length = bs.length := by simpa using hlen
          have h1' : ∀ x ∈ as, ‖x‖ ≤ 1 := fun x hx => h1 x (by simp [hx])
          have h2' : ∀ x ∈ bs, ‖x‖ ≤ 1 := fun x hx => h2 x (by simp [hx])
          have hpa : ‖as.prod‖ ≤ 1 := norm_list_prod_le_one h1'
          have hsplit : a * as.prod - b * bs.prod
              = (a - b) * as.prod + b * (as.prod - bs.prod) := by noncomm_ring
          rw [hsplit]
          calc ‖(a - b) * as.prod + b * (as.prod - bs.prod)‖
              ≤ ‖(a - b) * as.prod‖ + ‖b * (as.prod - bs.prod)‖ := norm_add_le _ _
            _ ≤ ‖a - b‖ * ‖as.prod‖ + ‖b‖ * ‖as.prod - bs.prod‖ :=
                add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
            _ ≤ ‖a - b‖ * 1 + 1 * ‖as.prod - bs.prod‖ := by
                refine add_le_add ?_ ?_
                · exact mul_le_mul_of_nonneg_left hpa (norm_nonneg _)
                · exact mul_le_mul (h2 b (by simp)) le_rfl (norm_nonneg _) zero_le_one
            _ = ‖a - b‖ + ‖as.prod - bs.prod‖ := by ring
            _ ≤ ‖a - b‖ + (as.zipWith (fun a b => ‖a - b‖) bs).sum := by
                gcongr
                exact ih bs hlen' h1' h2'

end Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian
