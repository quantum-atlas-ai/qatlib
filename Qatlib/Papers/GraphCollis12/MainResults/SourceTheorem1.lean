/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis12.MainResults.SourceLemma8

set_option backward.isDefEq.respectTransparency false

/-!
# GraphCollis12 — Theorem 1 (query complexity of the §4 algorithm)

Fixed source: arXiv:1204.1527v1, §1.1 p.2 (statement) and §4 pp.5–6 (proof):

> Theorem 1. For a graph `G` on `n` vertices, the quantum query complexity of the
> graph collision problem on `G` is `O(√n + √(α*(G)))`.

The §4 algorithm has three steps (p.5):
1. compute `α*(G)` (no queries to `x`), set `s = max{α*(G), n}`;
2. preprocessing: approximate counting (Corollary 6, [BHT98]) with `P = ⌈7π√n⌉`
   costs `O(P) = O(√n)` queries;
3. main case: Lemma 7(ii) with `k = 2s` costs `O(√n + √(2s))` queries.

The §4 "Query complexity" paragraph concludes: `O(√n) + O(√n + √(2s)) = O(√n + √(α*(G)))`
because `s = max{α*(G), n}`.

This file formalises the *query-count accounting* — the §4 step that is purely
arithmetic once the two per-step bounds are supplied.  The per-step bounds come
from the cited results: `hCount` is [BHT98] Corollary 6 (`O(P) = O(√n)` with
`P = ⌈7π√n⌉`), and `hMain` is Lemma 7(ii) (`O(√n + √k)` with `k = 2s`), whose
span-program witness-size core is `...MainResults.SourceLemma7`.

Because the repository has no formal models of *quantum query algorithms*, the
two step-cost functions `costCounting`, `costMain` are taken as parameters with
the documented interpretation "number of oracle queries made by step 2 / step 3";
the conclusion bounds their sum, which is the query complexity of the §4
algorithm and hence an upper bound on the worst-case complexity `Q(G)`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.GraphCollis12.MainResults

/-- `s = max{α*(G), n}` of step 1 (§4, p.5). -/
def stepScale {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := max (alphaStar G) n

/-- `k = 2s` of step 3 (§4, p.5). -/
def stepK {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := 2 * stepScale G

/-- The step cost functions dominate the two per-step query counts. -/
theorem theorem1_step_bounds_cost {n : ℕ}
    (costCounting costMain : SimpleGraph (Fin n) → ℝ)
    (hCount : ∃ a : ℝ, 0 < a ∧ ∀ G, costCounting G ≤ a * Real.sqrt (n : ℝ))
    (hMain : ∃ b : ℝ, 0 < b ∧
      ∀ G, costMain G ≤ b * (Real.sqrt (n : ℝ) + Real.sqrt (stepK G : ℝ))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ G, costCounting G + costMain G ≤
        c * (Real.sqrt (n : ℝ) + Real.sqrt (alphaStar G : ℝ)) := by
  obtain ⟨a, hapos, ha⟩ := hCount
  obtain ⟨b, hbpos, hb⟩ := hMain
  refine ⟨a + b * (1 + Real.sqrt 2) + b * Real.sqrt 2, ?_, ?_⟩
  · positivity
  intro G
  have hn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have haG := ha G
  have hbG := hb G
  -- `stepK G = 2 * max(α*, n)`, so `√(stepK G) ≤ √2 (√(α*) + √n)`.
  have hk : Real.sqrt ((stepK G : ℕ) : ℝ) ≤
      Real.sqrt 2 * (Real.sqrt (alphaStar G : ℝ) + Real.sqrt (n : ℝ)) := by
    have hcast : ((stepK G : ℕ) : ℝ) = 2 * ((max (alphaStar G) n : ℕ) : ℝ) := by
      simp [stepK, stepScale]
    rw [hcast]
    have hmax : ((max (alphaStar G) n : ℕ) : ℝ) ≤ (alphaStar G : ℝ) + (n : ℝ) := by
      have hmn : (max (alphaStar G) n : ℕ) ≤ alphaStar G + n := by
        exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      exact_mod_cast hmn
    have h2max : 2 * ((max (alphaStar G) n : ℕ) : ℝ) ≤
        2 * ((alphaStar G : ℝ) + (n : ℝ)) := by linarith
    refine le_trans (Real.sqrt_le_sqrt h2max) ?_
    -- `√(2(x+y)) ≤ √(2x) + √(2y)`
    have hxy : Real.sqrt (2 * ((alphaStar G : ℝ) + (n : ℝ))) ≤
        Real.sqrt (2 * (alphaStar G : ℝ)) + Real.sqrt (2 * (n : ℝ)) := by
      rw [show 2 * ((alphaStar G : ℝ) + (n : ℝ))
            = 2 * (alphaStar G : ℝ) + 2 * (n : ℝ) from by ring]
      have hx' : (0 : ℝ) ≤ 2 * (alphaStar G : ℝ) := by positivity
      have hy' : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
      have hsq : 2 * (alphaStar G : ℝ) + 2 * (n : ℝ) ≤
          (Real.sqrt (2 * (alphaStar G : ℝ)) + Real.sqrt (2 * (n : ℝ))) ^ 2 := by
        rw [add_sq, Real.sq_sqrt hx', Real.sq_sqrt hy']
        nlinarith [Real.sqrt_nonneg (2 * (alphaStar G : ℝ)),
          Real.sqrt_nonneg (2 * (n : ℝ))]
      have hsum_nn : (0 : ℝ) ≤
          Real.sqrt (2 * (alphaStar G : ℝ)) + Real.sqrt (2 * (n : ℝ)) := by positivity
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hsum_nn] at this
    refine le_trans hxy ?_
    rw [show Real.sqrt (2 * (alphaStar G : ℝ)) = Real.sqrt 2 * Real.sqrt (alphaStar G : ℝ) from
        Real.sqrt_mul (by norm_num) _,
      show Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) from
        Real.sqrt_mul (by norm_num) _]
    have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [Real.sqrt_nonneg (alphaStar G : ℝ), Real.sqrt_nonneg (n : ℝ)]
  have hsum : costCounting G + costMain G ≤
      a * Real.sqrt (n : ℝ) + b * (Real.sqrt (n : ℝ) +
        Real.sqrt 2 * (Real.sqrt (alphaStar G : ℝ) + Real.sqrt (n : ℝ))) := by
    have hb' : b * (Real.sqrt (n : ℝ) + Real.sqrt (stepK G : ℝ)) ≤
        b * (Real.sqrt (n : ℝ) +
          Real.sqrt 2 * (Real.sqrt (alphaStar G : ℝ) + Real.sqrt (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hbpos)
      linarith
    linarith
  refine le_trans hsum ?_
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsa : (0 : ℝ) ≤ Real.sqrt (alphaStar G : ℝ) := Real.sqrt_nonneg _
  have hbase : a * Real.sqrt (n : ℝ) + b * (Real.sqrt (n : ℝ) +
        Real.sqrt 2 * (Real.sqrt (alphaStar G : ℝ) + Real.sqrt (n : ℝ)))
      ≤ (a + b * (1 + Real.sqrt 2) + b * Real.sqrt 2) * Real.sqrt (n : ℝ)
        + (a + b * (1 + Real.sqrt 2) + b * Real.sqrt 2) * Real.sqrt (alphaStar G : ℝ) := by
    nlinarith [hsa, hn, hs2, hapos, hbpos, mul_nonneg (le_of_lt hbpos) hsa,
      mul_nonneg (le_of_lt hbpos) hn]
  nlinarith [hbase]

/-- **Theorem 1** (arXiv:1204.1527v1, §1.1 p.2, proved §4 pp.5–6).  The two-step
algorithm of §4 makes at most `O(√n + √(α*(G)))` oracle queries to `x`; its query
count is an upper bound on the worst-case quantum query complexity of the graph
collision problem on `G`. -/
theorem theorem1_query_count_bound {n : ℕ}
    (costCounting costMain : SimpleGraph (Fin n) → ℝ)
    (hCount : ∃ a : ℝ, 0 < a ∧ ∀ G, costCounting G ≤ a * Real.sqrt (n : ℝ))
    (hMain : ∃ b : ℝ, 0 < b ∧
      ∀ G, costMain G ≤ b * (Real.sqrt (n : ℝ) + Real.sqrt (stepK G : ℝ))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ G, costCounting G + costMain G ≤
        c * (Real.sqrt (n : ℝ) + Real.sqrt (alphaStar G : ℝ)) :=
  theorem1_step_bounds_cost costCounting costMain hCount hMain

end Qatlib.Papers.GraphCollis12.MainResults
