/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QueryBudget — the query bound of Lemma 4.2

Wu--Yang--Yao, fixed arXiv:2511.17227v2, Section 4, Algorithm 1.

The analysis of Algorithm 1 uses the potential function

`Δ(U,V,J) = 2b|J| - H∞(X_J) - H∞(Y_J)`.

Over the `c` iterations of the classical for-loop the potential gains at most `c`
(at most one bit per transmitted classical bit, plus a bounded loss from the
candidate `I ⊆ J`), while every removal of a coordinate subset `I` from `J` lowers
it by at least `(b - 0.99b - 1 - 1/|I|)` per coordinate, which the paper bounds by
`0.005b|I|`. Since `Δ ≥ 0` throughout, at most `200c/b` coordinates are queried.

This module records the final numerical step. The potential-function invariant
itself — that it starts at `0`, gains at most `c`, and loses at least `0.005b|I|`
per removed `I` — is the part of Lemma 4.2 not formalized here.

Boundary: only the arithmetic conclusion `Q ≤ 200c/b` from
`0.005·b·Q ≤ c` is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LiftingWu25.HybridTree

/-- If the total potential cost of the queried coordinates, `0.005·b` per query, is at
most the `c` classical bits, then at most `200c/b` coordinates are queried. -/
theorem query_budget {c b q : ℝ} (hb : 0 < b) (hΔ : q * (0.005 * b) ≤ c) :
    q ≤ 200 * c / b := by
  have hq : q * 0.005 * b ≤ c := by linarith
  rw [le_div_iff₀ hb]
  nlinarith

/-- The same bound for a natural number of queried coordinates, in the form used by
`Tradeoff.theorem52_degree_core`. -/
theorem query_budget_nat {c b : ℝ} (hb : 0 < b) (q : ℕ)
    (hΔ : (q : ℝ) * (0.005 * b) ≤ c) : (q : ℝ) ≤ 200 * c / b :=
  query_budget hb hΔ

end Qatlib.Papers.LiftingWu25.HybridTree
