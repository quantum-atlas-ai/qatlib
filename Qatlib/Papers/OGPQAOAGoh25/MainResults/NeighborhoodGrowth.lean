/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! Neighborhood-growth lemmas for
"The Overlap Gap Property limits limit swapping in the QAOA"
(arXiv:2404.06087v6, 2025, Mark Goh).

Lemmas 4.5–4.7 of the paper fix an average degree `λ` and a locality
radius `l ≤ ε log n`, and show that almost all `l`-local neighbourhoods
of the random hypergraph are treelike; the branching-process intuition
is that an `l`-neighbourhood grown at rate `λ` has size `λ^l`, which
stays polynomial in `n` precisely because the depth is capped at
`ε log n`.

- `geometric_growth` is the closed form of such a branching process
  (`ball (k+1) = λ • ball k`, `ball 0 = 1` gives `ball l = λ^l`).
- `depth_cap_bounds_growth` is the deterministic depth-cap core of
  Lemma 4.7: if `l ≤ log n / log λ` with `λ > 1`, then the `λ`-grown
  neighbourhood size is at most `n`. This is the arithmetic that makes
  "ε log n-local" a sublinear-depth regime.

The probabilistic w.h.p. statements themselves (random hypergraph
concentration, cycle counts) are not formalized here; see the PR work
log.

No axiom, no `admit`, no `native_decide`. -/
set_option autoImplicit false

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults.NeighborhoodGrowth

/-- **Lemmas 4.5–4.7, branching-process core**: a radius counter that
starts at `1` and grows by a factor `rate` per level satisfies
`ball l = rate ^ l` for every radius `l`. -/
theorem geometric_growth (rate : ℝ) (ball : ℕ → ℝ)
    (h0 : ball 0 = 1) (hg : ∀ k : ℕ, ball (k + 1) = rate * ball k) (l : ℕ) :
    ball l = rate ^ l := by
  induction l with
  | zero => simpa using h0
  | succ k ih => rw [hg, ih, pow_succ, mul_comm]

/-- **Lemma 4.7, deterministic depth-cap core**: with branching factor
`rate > 1`, any radius `l` satisfying `l ≤ log n / log rate` keeps the
grown neighbourhood `rate ^ l` within the vertex count `n ≥ 1`. This is
the arithmetic content of the `p ≤ ε log n` locality cap: exponential
growth stays below the instance size. -/
theorem depth_cap_bounds_growth (rate : ℝ) (hrate : 1 < rate) {l n : ℕ} (hn : 1 ≤ n)
    (hl : (l : ℝ) ≤ Real.log n / Real.log rate) :
    rate ^ (l : ℝ) ≤ n := by
  have hposrate : (0:ℝ) < rate := lt_trans zero_lt_one hrate
  have hlograte : 0 < Real.log rate := Real.log_pos hrate
  have hnreal : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  refine (Real.log_le_log_iff (Real.rpow_pos_of_pos hposrate _) hnreal).mp ?_
  rw [Real.log_rpow hposrate]
  exact (mul_le_mul_of_nonneg_right hl hlograte.le).trans_eq (div_mul_cancel₀ _ hlograte.ne')

end Qatlib.Papers.OGPQAOAGoh25.MainResults.NeighborhoodGrowth
