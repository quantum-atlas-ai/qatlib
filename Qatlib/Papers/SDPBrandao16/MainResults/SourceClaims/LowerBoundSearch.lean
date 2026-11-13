/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Concepts.SearchStopping.QueryLowerBound.FixedQueryLowerBound

set_option backward.isDefEq.respectTransparency false

/-!
# Source §2.3 — `Ω(√n + √m)` quantum / `Ω(n + m)` classical lower bound
(Brandão–Svore 2016)

Fixed source: arXiv:1609.05537v5, §2.3 "Lower Bounds", printed page 8.

The source exhibits two families of primal SDP instances (dimension `n`,
`m` constraints) that differ only in the position of a marked pair `(i, j)`,
and argues:

> "to decide which of the two cases we are given requires at least `Ω(n+m)`
> calls to the oracle classically and `Ω(√n + √m)` calls quantum-mechanically.
> This follows from an elementary reduction to the search problem."

**Reduction.** Deciding the two cases is equivalent to solving two independent
search problems, one over the `n` possible `i` and one over the `m` possible
`j`.  A `r`-query decision algorithm therefore yields, on the family where one
of the two searches is trivial, a `r`-query search algorithm on the other
subproblem; with dedicated budgets `r_n + r_m ≤ r` this gives the sum bound.

* **quantum.** The established `fixed_query_quadratic_bound` (reused below through
  `search_lowerBound_from_frozen`) gives, for any fixed-budget quantum search
  algorithm with average success at least `1/2`,
  `(1 − √2/2) N − √N ≤ 2 r²`, whence `r ≥ √N / 4` for `N ≥ 64`.
* **classical.** A deterministic search that identifies the marked index of a
  length-`n` list must query all but at most one coordinate, `r ≥ n − 1`
  (proved below by a transcript argument).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Concepts.SearchStopping.QueryLowerBound
open scoped BigOperators

/-! ## §1 Bridge to the fixed-budget quantum search lower bound -/

/-- **Reuse of the fixed-budget quantum search lower bound.**

A `r`-query quantum search algorithm on a uniformly random target `y` in a
finite `Y` (with any finite ancillary `C`), agreeing with the real oracle on
all `n < r` queries and succeeding with average Born probability at least
`1/2`, satisfies `(1 − √2/2) |Y| − √|Y| ≤ 2 r²`.

The theorem used here is:
`Qatlib.Concepts.SearchStopping.QueryLowerBound.fixed_query_quadratic_bound`. -/
theorem search_lowerBound_from_frozen {C Y : Type*}
    [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : Y → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (f : ℕ → C → Option Y) (ψ : EuclideanSpace ℂ C) (hψ : ‖ψ‖ = 1) (r : ℕ)
    (hagree : ∀ y n, n < r → ∀ c, f n c ≠ some y →
      V y n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1))
    (hsuccess : (Fintype.card Y : ℝ) / 2 ≤
      ∑ y : Y, QuerySuccess (f r) (UnitaryEvolution (V y) ψ r) y) :
    (1 - Real.sqrt 2 / 2) * (Fintype.card Y : ℝ) - Real.sqrt (Fintype.card Y) ≤
      2 * (r : ℝ) ^ 2 :=
  fixed_query_quadratic_bound U V f ψ hψ r hagree hsuccess

/-! ## §2 From the quadratic bound to `r ≥ √N / 4` -/

/-- **Quantum search budget (`N ≥ 64`).**

From the quadratic bound `(1 − √2/2) N − √N ≤ 2 r²` with `N ≥ 64`, a
fixed-budget search algorithm needs `r ≥ √N / 4`. -/
theorem searchBudget_quarter (N r : ℕ) (hN : 64 ≤ N)
    (h : (1 - Real.sqrt 2 / 2) * (N : ℝ) - Real.sqrt (N : ℝ) ≤ 2 * (r : ℝ) ^ 2) :
    Real.sqrt (N : ℝ) / 4 ≤ (r : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  -- `√2 < 3/2`, hence `1 − √2/2 > 1/4`.
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hcoef : (1 : ℝ) / 4 ≤ 1 - Real.sqrt 2 / 2 := by linarith
  -- `8 ≤ √N` because `64 ≤ N`.
  have h8 : (8 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hN64 : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [hspos, hsq, hN64]
  -- `√N ≤ N / 8` for `√N ≥ 8`.
  have hle : Real.sqrt (N : ℝ) ≤ (N : ℝ) / 8 := by
    have hmul := mul_le_mul_of_nonneg_right h8 hspos.le
    rw [← pow_two, hsq] at hmul
    linarith
  -- `2 r² ≥ (1 − √2/2) N − √N ≥ N/4 − N/8 = N/8`.
  have hcoefN : (N : ℝ) / 4 ≤ (1 - Real.sqrt 2 / 2) * (N : ℝ) := by
    have := mul_le_mul_of_nonneg_right hcoef hNpos.le
    linarith
  have hr2 : (N : ℝ) / 16 ≤ (r : ℝ) ^ 2 := by linarith
  have hrn : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hroot : Real.sqrt ((N : ℝ) / 16) ≤ (r : ℝ) := by
    rw [← Real.sqrt_sq hrn]
    exact Real.sqrt_le_sqrt hr2
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hdiv : Real.sqrt ((N : ℝ) / 16) = Real.sqrt (N : ℝ) / 4 := by
    rw [Real.sqrt_div hNpos.le (16 : ℝ), h16]
  rw [hdiv] at hroot
  linarith

/-! ## §3 Classical search needs `N − 1` queries -/

/-- **Classical deterministic search needs `N − 1` queries.**

Model a deterministic classical algorithm by the set `Q : Finset (Fin N)` of
coordinates it queries (its transcript on an instance is the answer string
restricted to `Q`).  Correctness means two instances that agree on `Q` must
have the same marked index (`hcorrect`).  Then two distinct indices both
outside `Q` would agree on `Q`, so at most one index lies outside `Q`, i.e.
`N − 1 ≤ |Q| ≤ r`. -/
theorem classical_search_needs_card_sub_one (N r : ℕ) (Q : Finset (Fin N))
    (hQ : Q.card ≤ r)
    (hcorrect : ∀ i j : Fin N, (∀ q ∈ Q, (q = i) = (q = j)) → i = j) :
    N - 1 ≤ r := by
  have hcard : (Finset.univ \ Q).card = N - Q.card := by
    rw [Finset.card_sdiff]
    simp [Finset.card_univ, Fintype.card_fin]
  have hle1 : (Finset.univ \ Q).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
    exact hcorrect a b (fun q hq => by
      have hqa : q ≠ a := fun h => ha (h ▸ hq)
      have hqb : q ≠ b := fun h => hb (h ▸ hq)
      simp only [hqa, hqb])
  omega

/-! ## §4 The assembed lower bounds -/

/-- **Source §2.3 — quantum lower bound (printed p. 8).**

A decision algorithm for the two SDP families that induces a `r_n`-query
quantum search algorithm on the `n`-part and a `r_m`-query one on the `m`-part,
with the quadratic bounds `hredN`, `hredM` supplied by
`search_lowerBound_from_frozen`, and dedicated budgets `r_n + r_m ≤ r`, needs
`(√n + √m) / 4 ≤ r`, i.e. `r = Ω(√n + √m)` quantum queries. -/
theorem lowerBound_quantum (n m rn rm r : ℕ) (hn : 64 ≤ n) (hm : 64 ≤ m)
    (hbudget : rn + rm ≤ r)
    (hredN : (1 - Real.sqrt 2 / 2) * (n : ℝ) - Real.sqrt (n : ℝ) ≤ 2 * (rn : ℝ) ^ 2)
    (hredM : (1 - Real.sqrt 2 / 2) * (m : ℝ) - Real.sqrt (m : ℝ) ≤ 2 * (rm : ℝ) ^ 2) :
    (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) / 4 ≤ (r : ℝ) := by
  have hn' := searchBudget_quarter n rn hn hredN
  have hm' := searchBudget_quarter m rm hm hredM
  have hbudget' : (rn : ℝ) + (rm : ℝ) ≤ (r : ℝ) := by exact_mod_cast hbudget
  linarith

/-- **Source §2.3 — classical lower bound (printed p. 8).**

A decision algorithm for the two SDP families that induces a `r_n`-query
classical search on the `n`-part and a `r_m`-query one on the `m`-part, with
the per-subproblem requirements `n − 1 ≤ r_n`, `m − 1 ≤ r_m` supplied by
`classical_search_needs_card_sub_one`, and dedicated budgets `r_n + r_m ≤ r`,
needs `n + m − 2 ≤ r`, i.e. `r = Ω(n + m)` classical queries. -/
theorem lowerBound_classical (n m rn rm r : ℕ)
    (hbudget : rn + rm ≤ r) (hn : n - 1 ≤ rn) (hm : m - 1 ≤ rm) :
    n + m - 2 ≤ r := by
  omega

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
