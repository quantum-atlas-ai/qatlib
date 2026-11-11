/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults.QueryCount — recursive DB-DOI query count `(2n+1)^k` (c003)

Fixed source: arXiv:2408.03987, Sec. II C ("Explicit unfolding of DB-DOI with
warm-start"), text following Eqs. (8), (23) and (25).

The paper unfolds the DB-DOI recursion until every unitary is generated either
by `D` or by `H_0`. Each unfolding of a step replaces one occurrence of the
previous unitary `U_{k-1}` by `2n+1` copies, where `n` is the number of
evolution operators in the chosen product formula. Hence `k` steps need
`(2n+1)^k` queries, and the circuit depth grows exponentially with `k`.

* Eq. (25) (higher-order formula) has `n = 2`, giving `5^k` queries;
* Eq. (8) (minimal first-order formula) has `n = 1`, giving `3^k` queries.

This is a purely combinatorial recursion; the formalisation below defines the
count by the recursion and proves the closed form and its two instances. It is
a complete proof (no `sorry`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.GroundDBrak24.MainResults.QueryCount

/-- Number of queries after `k` recursive DB-DOI unfoldings when the product
formula at each level contains `n` evolution operators (Eqs. (8), (23), (25)).
Base case `Q(0) = 1` (the top-level word); each unfolding multiplies the count
by `2n+1`. -/
def queryCount (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (2 * n + 1) * queryCount n k

/-- c003, Sec. II C: `k` recursive DB-DOI unfoldings require `(2n+1)^k` queries
when the product formula has `n` evolution operators. -/
theorem queryCount_eq_pow (n k : ℕ) : queryCount n k = (2 * n + 1) ^ k := by
  induction k with
  | zero => simp [queryCount]
  | succ k ih =>
      rw [queryCount, ih, pow_succ]
      ring

/-- c003, the `n = 2` instance of Eq. (25): the higher-order DB-DOI formula
entails `5^k` queries. -/
theorem second_order_queryCount (k : ℕ) : queryCount 2 k = 5 ^ k := by
  simp [queryCount_eq_pow]

/-- c003, the `n = 1` instance of Eq. (8): the minimal first-order formula
requires only `3^k` queries. -/
theorem first_order_queryCount (k : ℕ) : queryCount 1 k = 3 ^ k := by
  simp [queryCount_eq_pow]

/-- c003, exponential depth growth: for any product formula with `n ≥ 1`
evolution operators, `2^k ≤ (2n+1)^k`, so the circuit depth grows exponentially
with the number of steps `k`. -/
theorem queryCount_exponential_growth (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    2 ^ k ≤ queryCount n k := by
  rw [queryCount_eq_pow]
  exact pow_le_pow_left' (by omega : 2 ≤ 2 * n + 1) k

end Qatlib.Papers.GroundDBrak24.MainResults.QueryCount
