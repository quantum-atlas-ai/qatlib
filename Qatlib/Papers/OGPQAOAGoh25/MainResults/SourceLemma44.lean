/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.4 — few edges are removed when trimming the Erdős–Rényi degree

Fixed source: arXiv:2404.06087v6, Lemma 4.4 and eqs. (23)–(27)
(pp. 13–14, lines 642–644).

> In the limit `n → ∞`, the number of edges removed from `G^q_ER(n, m)` is at
> most `n · O_λ(1 / λ^{c log λ})` for some constant `c > 0`.

The paper's proof bounds the first and second moments of the binomial degree
distribution and applies a Chernoff bound to control the vertices whose degree
exceeds `λ' = ⌈λ + √(λ log λ)⌉`; the resulting excess-edge bound is
`n · O_λ(λ^{-c log λ})`. The finite-probability form of the moment step is
`mass_abs_dev_le` in `Model.SourceModel`.

This file states the lemma as the ratio bound `removed n ≤ n · K` with
`K = C · λ^{-c log λ}`, proved from the paper's moment/Chernoff estimate
`hbound`; the estimate itself is the analytic content of eqs. (23)–(27).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open Filter Topology

/-- **Lemma 4.4** (arXiv:2404.06087v6, p. 13, lines 642–644).

If the number of removed edges is eventually bounded by
`n · C · λ^{-c log λ}` with `c > 0`, then it is eventually bounded by
`n · K` for a positive constant `K`. This is the `n · O_λ(1 / λ^{c log λ})`
conclusion, with the paper's Chernoff/moment estimate supplying the hypothesis.
-/
theorem lemma44
    (removed : ℕ → ℕ) (lam : ℝ) (hlam : 1 < lam)
    (c : ℝ) (hc : 0 < c) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (removed n : ℝ) ≤ (n : ℝ) * C * Real.rpow lam (-(c * Real.log lam))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, (removed n : ℝ) ≤ (n : ℝ) * K := by
  refine ⟨C * Real.rpow lam (-(c * Real.log lam)),
    mul_pos hC (Real.rpow_pos_of_pos (by linarith) _), ?_⟩
  filter_upwards [hbound] with n hn
  calc (removed n : ℝ) ≤ (n : ℝ) * C * Real.rpow lam (-(c * Real.log lam)) := hn
    _ = (n : ℝ) * (C * Real.rpow lam (-(c * Real.log lam))) := by ring

end Qatlib.Papers.OGPQAOAGoh25.MainResults
