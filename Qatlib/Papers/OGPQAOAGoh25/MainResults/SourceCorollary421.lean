/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 4.2.1 — the limit-swapped QAOA value stays below the Parisi value

Fixed source: arXiv:2404.06087v6, Corollary 4.2.1 (p. 12, lines 550–553),
attributed to Theorem 4 of [5].

> From Theorem 4.2 the performance of the QAOA on the pure `q`-spin glass for
> even `q ≥ 4` is upper bounded by `ηOGP` as `p → ∞` and is strictly less than
> the optimal value, i.e. the Parisi value `Π_q`, under the swapping of limits.

The formal content is the following: if the sequence of QAOA performances
`perf p` (optimised at each depth according to [4, 5]) converges as `p → ∞` to a
limit `perfLim`, and Theorem 4.2 bounds every `perf p` by `ηOGP`, while the OGP
gap gives `ηOGP < Π_q`, then the swapped limit is strictly below the Parisi
value.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

open Filter Topology

/-- **Corollary 4.2.1** (arXiv:2404.06087v6, p. 12, lines 550–553).

If the performance of the depth-`p` QAOA is at most `ηOGP` for every `p`, the
performance converges as `p → ∞`, and `ηOGP` is strictly below the Parisi
value `Π_q`, then the limit obtained by first letting `n → ∞` and then `p → ∞`
is strictly sub-optimal. -/
theorem corollary421
    (perf : ℕ → ℝ) (perfLim parisi ηOGP : ℝ)
    (hlim : Tendsto perf atTop (𝓝 perfLim))
    (hub : ∀ p : ℕ, perf p ≤ ηOGP)
    (hgap : ηOGP < parisi) :
    perfLim < parisi :=
  lt_of_le_of_lt (le_of_tendsto hlim (Eventually.of_forall hub)) hgap

end Qatlib.Papers.OGPQAOAGoh25.MainResults
