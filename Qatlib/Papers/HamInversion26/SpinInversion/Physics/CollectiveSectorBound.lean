/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Cubic bound on the collective-spin sector count

Supplement of arXiv:2607.29382v2, Eqs. (S105)–(S106), page S22, and Corollary 2 of the
Letter, page 4.  After removing the Schur–Weyl factors, the collective-spin family splits
into sectors indexed by `j = 0, …, ⌊n/2⌋` of dimension `d_j = n − 2j + 1`, and the sum of the
squares of the sector dimensions is what the blockwise completion counts:

`Σ_{j} d_j² = Σ_{j=0}^{⌊n/2⌋} (n − 2j + 1)²`.

This module proves the elementary explicit bound `Σ_j (n − 2j + 1)² ≤ (n + 1)³`, which is the
`O(n³)` half of `q_col = O(n³)` in Corollary 2: there are at most `n + 1` sectors of
dimension at most `n + 1`.  The asymptotics as a limit statement (`IsBigO`), the query-count
assembly `q_col ≤ Σ_j [q_univ(d_j) + 1] − 1` and the `O(4ⁿ)` comparison with a
dimension-only inverter are not part of this module.
-/

open Finset
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Physics

set_option autoImplicit false

/-- **Cubic collective-sector bound** (Eqs. (S105)–(S106), page S22; Corollary 2, page 4): the
sum of the squared active dimensions `n − 2j + 1` of the collective-spin sectors is at most
`(n + 1)³`. -/
theorem sum_sq_dim_bound (n : ℕ) :
    (∑ j ∈ Finset.range (n / 2 + 1), (n - 2 * j + 1) ^ 2) ≤ (n + 1) ^ 3 := by
  calc (∑ j ∈ Finset.range (n / 2 + 1), (n - 2 * j + 1) ^ 2)
      ≤ ∑ _j ∈ Finset.range (n / 2 + 1), (n + 1) ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have h : n - 2 * j + 1 ≤ n + 1 := by omega
        exact Nat.pow_le_pow_left h 2
    _ = (n / 2 + 1) * (n + 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
    _ ≤ (n + 1) * (n + 1) ^ 2 := by
        exact Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) ^ 3 := by ring

end Qatlib.Papers.HamInversion26.SpinInversion.Physics
