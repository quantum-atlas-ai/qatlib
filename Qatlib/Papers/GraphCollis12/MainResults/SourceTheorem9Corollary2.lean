/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.GraphCollis12.MainResults.SourceTheorem1

set_option backward.isDefEq.respectTransparency false

/-!
# GraphCollis12 — Theorem 9 and Corollary 2

Fixed source: arXiv:1204.1527v1, §5 (p.7):

> Theorem 9. There exists a universal constant `C` such that for any `p ∈ (0,1]`,
> `n ∈ ℕ` and `t ≥ 40 n log n`: for `G ∼ μ_{n,p}`, the probability that the
> (worst-case) quantum query complexity of graph collision on `G` is greater than
> `C(√n + √t)` is at most `n^{-14n} + 2 exp(-t²/(200 n² p))`.
>
> Corollary 2 (§1.1 p.2). For arbitrary `p : ℕ → [0,1]`, let `G ∼ μ_{n,p(n)}`.
> Then the (worst-case) quantum query complexity of graph collision on `G` is
> almost always `O(√(n log n))`.

Both follow "immediately from Theorem 1 and Lemma 8" (p.7):
* Theorem 1 gives `Q(G) ≤ c(√n + √(α*(G)))`, so whenever `α*(G) < t` we have
  `Q(G) < c(√n + √t)`; hence `{Q > c(√n+√t)} ⊆ {α* ≥ t}`, and Lemma 8 bounds the
  latter.
* Corollary 2 takes `t = 40 n log n`, where the Lemma 8 tail is
  `n^{-14n} + 2 exp(-8 (log n)²/p) ≤ n^{-14n} + 2 n^{-8 log n} → 0`, and
  `√(40 n log n) ≤ √40·√(n log n)`, `√n ≤ √(n log n)` for `n ≥ 3`.

`Q` is the (worst-case, two-sided-error) quantum query complexity, taken as an
abstract function; `hT1` is exactly the conclusion of Theorem 1
(`...MainResults.theorem1_query_count_bound`).
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.GraphCollis12.MainResults

/-- **Theorem 9** (arXiv:1204.1527v1, §5 p.7).  Given Theorem 1's bound
`Q(G) ≤ c(√n + √(α*(G)))` (`hT1`), there is a universal `C > 0` such that the
`μ_{n,p}`-probability that `Q(G) > C(√n + √t)` is at most
`n^{-14n} + 2 exp(-t²/(200 n² p))` for `t ≥ 40 n log n`.

**Status: statement registered as a `Prop`-valued definition; the proof is a
substantive gap** because it depends on the unproved Chernoff/union-bound core
`lemma8`. -/
def theorem9 (n : ℕ) (hn : 1 ≤ n) (Q : SimpleGraph (Fin n) → ℝ)
    (hT1 : ∃ c : ℝ, 0 < c ∧
      ∀ G, Q G ≤ c * (Real.sqrt (n : ℝ) + Real.sqrt (alphaStar G : ℝ))) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ t : ℝ,
    40 * (n : ℝ) * Real.log (n : ℝ) ≤ t →
    muPr p (fun (G : SimpleGraph (Fin n)) =>
        C * (Real.sqrt (n : ℝ) + Real.sqrt t) < Q G) ≤
      (n : ℝ) ^ (-(14 * (n : ℝ))) +
        2 * Real.exp (-(t ^ 2) / (200 * (n : ℝ) ^ 2 * p))

/-- `1 ≤ log n` for `n ≥ 3`, used to compare `√n` with `√(n log n)`. -/
theorem one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : (1 : ℝ) ≤ Real.log (n : ℝ) := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_three]
  have h3n : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  linarith

/-- **Corollary 2** (arXiv:1204.1527v1, §1.1 p.2).  For arbitrary `p : ℕ → (0,1]`
and `n ≥ 3`, given Theorem 1's bound, the probability that `Q(G)` exceeds
`C·√(n log n)` is at most `n^{-14n} + 2 n^{-8 log n}` (which tends to `0`); thus
the graph collision problem on `G ∼ μ_{n,p(n)}` is almost always
`O(√(n log n))`.

**Status: statement registered as a `Prop`-valued definition; the proof is a
substantive gap** because it depends on the unproved `theorem9` / `lemma8`. -/
def corollary2 (n : ℕ) (hn : 3 ≤ n) (Q : SimpleGraph (Fin n) → ℝ)
    (hT1 : ∃ c : ℝ, 0 < c ∧
      ∀ G, Q G ≤ c * (Real.sqrt (n : ℝ) + Real.sqrt (alphaStar G : ℝ)))
    (pfun : ℕ → ℝ) (hp0 : 0 < pfun n) (hp1 : pfun n ≤ 1) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    muPr (pfun n) (fun (G : SimpleGraph (Fin n)) =>
        C * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) < Q G) ≤
      (n : ℝ) ^ (-(14 * (n : ℝ))) + 2 * (n : ℝ) ^ (-(8 * Real.log (n : ℝ)))

end Qatlib.Papers.GraphCollis12.MainResults
