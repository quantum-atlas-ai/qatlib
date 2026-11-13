/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Approximation.ErrorBudget

/-!
# Finite budgets for modular-functor approximation

This module packages finite word-length and product-error bounds associated with Theorem 2.1 of
[FreedmanLarsenWang2000]. `blockDiagOne` extends a four-dimensional matrix by an identity block.

The stated estimates control products of already supplied bounded words and contraction
approximants, and derive a numerical success lower bound from an error budget.

## Main statements

* `theorem2_1_word_length_budget`: Combine uniform factor word lengths.
* `theorem2_1_error_accumulation`: Sum uniform factor tolerances to an error of at most one
  tenth.
* `theorem2_1_success_from_error`: Convert the supplied error bound into a three-quarter lower
  bound.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Approximation

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Extend a `4 × 4` complex matrix to a `(4 + k) × (4 + k)` matrix by adjoining an identity
block of size `k`. -/
def blockDiagOne (k : ℕ) (g : CM 4) : CM (4 + k) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin k) (Fin k) ℂ))

/-- A product of `bs.length` factors, each represented by a braid word of length at most `l`,
has a word of length at most `bs.length * l`; see [FreedmanLarsenWang2000]. -/
theorem theorem2_1_word_length_budget {G : Type*} [Group G] {m : ℕ} {σ : Fin m → G}
    {l : ℕ} {bs : List G} (hbs : ∀ b ∈ bs, BraidWord σ l b) :
    BraidWord σ (bs.length * l) bs.prod :=
  braidWord_list_prod hbs

/-- Equal-length nonempty lists of contractions with paired errors at most `1 / (10 * u.length)`
have product error at most one tenth; see [FreedmanLarsenWang2000]. -/
theorem theorem2_1_error_accumulation {R : Type*} [NormedRing R] [NormOneClass R]
    (u v : List R)
    (hlen : u.length = v.length) (hpos : 1 ≤ u.length)
    (hu : ∀ x ∈ u, ‖x‖ ≤ 1) (hv : ∀ x ∈ v, ‖x‖ ≤ 1)
    (hstep : ∀ p ∈ u.zipWith (fun a b => ‖a - b‖) v,
      p ≤ 1 / (10 * (u.length : ℝ))) :
    ‖u.prod - v.prod‖ ≤ 1 / 10 := by
  have h1 := norm_list_prod_sub_prod_le u v hlen hu hv
  have h2 : (u.zipWith (fun a b => ‖a - b‖) v).sum ≤ 1 / 10 := by
    have h3 := list_sum_le_length_mul hstep
    rw [List.length_zipWith, ← hlen, Nat.min_self, nat_mul_inv_ten u.length hpos] at h3
    exact h3
  exact le_trans h1 h2

/-- If `err ≤ 1 / 10`, then the quantity `1 - err` is at least three quarters; see
[FreedmanLarsenWang2000]. -/
theorem theorem2_1_success_from_error {err : ℝ} (h : err ≤ 1 / 10) :
    3 / 4 ≤ 1 - err :=
  success_ge_three_quarters h

end Qatlib.Papers.ModularFunct00.MainResults.Approximation
