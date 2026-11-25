/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamNANDTree07.MainResults.ParityLowerBound

@[expose] public section

/-!
# Finite orthogonal projection norm bound

The projected vectors in Section 5 are pairwise orthogonal and their
sum is orthogonal to the residual. Pythagoras yields the projection
norm bound in Eq. (5.9).
-/

set_option autoImplicit false

namespace Qatlib.Papers.HamNANDTree07.MainResults

open scoped BigOperators InnerProductSpace

/-- Pairwise orthogonal self-adjoint idempotents satisfy the finite squared-norm bound. -/
theorem proj_sum_le {K : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (P : Fin K → V → V)
    (hidem : ∀ j x, P j (P j x) = P j x)
    (horth : ∀ i j, i ≠ j → ∀ x y, inner ℂ (P i x) (P j y) = 0)
    (hself : ∀ j x y, inner ℂ (P j x) y = inner ℂ x (P j y)) (x : V) :
    (∑ j, ‖P j x‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  let y : V := ∑ j, P j x
  have hrow (j : Fin K) : inner ℂ (P j x) y = inner ℂ (P j x) (P j x) := by
    rw [show y = ∑ i, P i x from rfl, inner_sum, Finset.sum_eq_single j]
    · intro i _ hij
      exact horth j i (Ne.symm hij) x x
    · simp
  have hdiag (j : Fin K) : inner ℂ (P j x) x = inner ℂ (P j x) (P j x) := by
    simpa only [hidem j x] using hself j (P j x) x
  have hres : inner ℂ y (x - y) = 0 := by
    rw [inner_sub_right]
    change inner ℂ (∑ j, P j x) x - inner ℂ (∑ j, P j x) y = 0
    simp only [sum_inner, hrow, hdiag, sub_self]
  have hy : ‖y‖ ^ 2 = ∑ j, ‖P j x‖ ^ 2 := by
    have hy' : inner ℂ y y = ∑ j, inner ℂ (P j x) (P j x) := by
      change inner ℂ (∑ j, P j x) y = _
      simp only [sum_inner, hrow]
    have hre := congrArg (RCLike.reLm (K := ℂ)) hy'
    simpa only [map_sum, RCLike.reLm_coe, inner_self_eq_norm_sq] using hre
  have hsum : y + (x - y) = x := by abel
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y (x - y) hres
  rw [hsum] at hpyth
  nlinarith only [hpyth, hy, sq_nonneg ‖x - y‖]

end Qatlib.Papers.HamNANDTree07.MainResults
