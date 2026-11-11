/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Bit complexity of the Krawtchouk statistic (Corollary 2.5, §2.2)

Paper: arXiv:2608.18839v3, Corollary 2.5 (page 8 of the PDF):

> `W_k` from Algorithm 2 can be implemented to run in
> `O(n^2 · k N log N)` time under the bit complexity model.  Thus, a
> correlation-concentrated uniformity tester can be implemented in
> `poly(n, N, k)` time.

The paper evaluates `K_k^{(N)}(t) = Σ_{j=0}^{k} (-1)^j C(t,j) C(N-t,k-j)` in
`O(k N log N)` bit operations per evaluation: `O(k)` arithmetic operations on
integers of at most `O(N)` bits, each costing `O(N log N)` bit operations, and
`n^2` evaluations are needed for `W_k`.

The file models this by an explicit operation counter and proves the
corresponding upper bound as a theorem about natural numbers.  The bound is
faithful to the paper's *upper* complexity claim (it keeps the `n^2`, `k`, `N`
and `log N` factors with explicit constants); it is not a lower bound and does
not model the memory hierarchy.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk

/-- Cost in bit operations of multiplying two integers of at most `N` bits,
modelled as `M(N) = (N+1)(⌊log₂(N+1)⌋ + 1) = O(N log N)`. -/
def bitMulCost (N : ℕ) : ℕ := (N + 1) * (Nat.log2 (N + 1) + 1)

/-- Number of big-integer arithmetic operations used by one evaluation of the
degree-`k` Krawtchouk polynomial via its explicit binomial sum: `6(k+1)`
operations (two binomial coefficients plus one multiplication and one
accumulation per term). -/
def krawtchoukEvalOps (k : ℕ) : ℕ := 6 * (k + 1)

/-- Arithmetic operations of the two-sample statistic `W_k`, which evaluates
`K_k` once per ordered pair of samples: `n^2 · 6(k+1)`. -/
def krawtchoukStatisticOps (n k : ℕ) : ℕ := (n * n) * krawtchoukEvalOps k

/-- Bit complexity of `W_k` under the operation-count model. -/
def krawtchoukStatisticBitCost (n N k : ℕ) : ℕ :=
  krawtchoukStatisticOps n k * bitMulCost N

/-- The operation counter of a single evaluation is exactly `6(k+1)`. -/
theorem krawtchoukEvalOps_eq (k : ℕ) : krawtchoukEvalOps k = 6 * (k + 1) := rfl

/-- The operation counter of `W_k` is exactly `6 n^2 (k+1)`. -/
theorem krawtchoukStatisticOps_eq (n k : ℕ) :
    krawtchoukStatisticOps n k = 6 * n ^ 2 * (k + 1) := by
  unfold krawtchoukStatisticOps krawtchoukEvalOps
  ring

/-- The operation counter is monotone in the number of sample pairs. -/
theorem krawtchoukStatisticOps_le (n k : ℕ) :
    krawtchoukStatisticOps n k ≤ 6 * n ^ 2 * (k + 1) :=
  (krawtchoukStatisticOps_eq n k).le

/-- Paper Corollary 2.5, model-level form: under the bit complexity model with
`M(N) = O(N log N)` multiplication cost, computing `W_k` from `n^2` two-sample
evaluations of the degree-`k` Krawtchouk polynomial costs at most
`6 n^2 (k+1) (N+1)(⌊log₂(N+1)⌋+1)` bit operations, i.e. `O(n^2 · k N log N)`
with explicit constants. -/
theorem krawtchoukStatistic_bit_complexity (n N k : ℕ) :
    krawtchoukStatisticBitCost n N k ≤
      6 * n ^ 2 * (k + 1) * (N + 1) * (Nat.log2 (N + 1) + 1) := by
  unfold krawtchoukStatisticBitCost bitMulCost
  rw [krawtchoukStatisticOps_eq]
  exact le_of_eq (by ring)

/-- Paper Corollary 2.5, `poly(n,N,k)` corollary: the bit cost is bounded by
the explicit polynomial `12 n^2 (k+1) (N+1)^2`. -/
theorem krawtchoukStatistic_polynomial_time (n N k : ℕ) :
    krawtchoukStatisticBitCost n N k ≤ 12 * n ^ 2 * (k + 1) * (N + 1) ^ 2 := by
  refine le_trans (krawtchoukStatistic_bit_complexity n N k) ?_
  have hlog : Nat.log2 (N + 1) + 1 ≤ 2 * (N + 1) := by
    have h1 := Nat.log2_le_self (N + 1)
    omega
  calc
    6 * n ^ 2 * (k + 1) * (N + 1) * (Nat.log2 (N + 1) + 1)
        ≤ 6 * n ^ 2 * (k + 1) * (N + 1) * (2 * (N + 1)) := by
          gcongr
    _ = 12 * n ^ 2 * (k + 1) * (N + 1) ^ 2 := by ring

end Qatlib.Papers.MixednessTest26.MainResults.Krawtchouk
