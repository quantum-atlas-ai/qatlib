/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Unary register resource bounds

This module records elementary counting inequalities for the unary encoding discussed in
[PoulinEtAl2018]. It bounds a sum of internal-node counts and the number of nonempty registers
by the total positions, and compares linear and logarithmic resource expressions.

## Main statements

* `treeInternalNodes_le_two_mul`: the summed internal-node count is at most twice the total
  positions.
* `registers_le_positions`: nonempty registers are no more numerous than their positions.
* `unary_third_level_le_binary`: `2 * N ≤ N * (Nat.log2 N + 1)` for `N ≥ 2`.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralMeas17.UnaryLedger

/-- The sum of the natural differences `N k - 1`, counting internal nodes for the register sizes
with subtraction truncated at zero. -/
def treeInternalNodes {K : ℕ} (N : Fin K → ℕ) : ℕ := ∑ k, (N k - 1)

/-- If the register sizes sum to `Ntot`, their summed internal-node count is at most `2 * Ntot`,
an elementary unary resource bound for [PoulinEtAl2018]. -/
theorem treeInternalNodes_le_two_mul {K : ℕ} (N : Fin K → ℕ) (Ntot : ℕ)
    (hsum : ∑ k, N k = Ntot) : treeInternalNodes N ≤ 2 * Ntot := by
  have hle : treeInternalNodes N ≤ Ntot := by
    unfold treeInternalNodes
    calc ∑ k, (N k - 1) ≤ ∑ k, N k :=
          Finset.sum_le_sum (fun k _ => Nat.sub_le _ _)
      _ = Ntot := hsum
  omega

/-- If each of `K` registers has at least one position and the sizes sum to `Ntot`, then `K ≤
Ntot`, as used in the unary encoding resource count of [PoulinEtAl2018]. -/
theorem registers_le_positions {K : ℕ} (N : Fin K → ℕ) (Ntot : ℕ)
    (hpos : ∀ k, 1 ≤ N k) (hsum : ∑ k, N k = Ntot) : K ≤ Ntot := by
  have h1 : (∑ k : Fin K, (1 : ℕ)) ≤ ∑ k, N k :=
    Finset.sum_le_sum (fun k _ => hpos k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum] at h1
  simpa using h1

/-- For `N ≥ 2`, the linear resource expression `2 * N` is at most `N * (Nat.log2 N + 1)`. -/
theorem unary_third_level_le_binary (N : ℕ) (hN : 2 ≤ N) :
    2 * N ≤ N * (Nat.log2 N + 1) := by
  have hlog : 1 ≤ Nat.log2 N := by
    rw [Nat.log2_eq_log_two, Nat.le_log_iff_pow_le Nat.one_lt_two (by omega : N ≠ 0)]
    simpa using hN
  calc 2 * N = N * 2 := by ring
    _ ≤ N * (Nat.log2 N + 1) := Nat.mul_le_mul_left N (by omega)

end Qatlib.Papers.SpectralMeas17.UnaryLedger
