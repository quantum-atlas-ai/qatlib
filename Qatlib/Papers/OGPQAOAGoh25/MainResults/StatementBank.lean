/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.OgpLandscape
import Qatlib.Papers.OGPQAOAGoh25.MainResults.QaoaValue
import Qatlib.Papers.OGPQAOAGoh25.MainResults.NeighborhoodGrowth

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"The Overlap Gap Property limits limit swapping in the QAOA"
(arXiv:2404.06087v6, 2025, Mark Goh).

This file records abstract `Prop` statements for the claims listed below.
Three mathematical components are proved in the accompanying modules:
`OgpLandscape.ogp_forbids_two_far_optima` and
`OgpLandscape.limit_swap_suboptimal` (c004, Corollary 4.2.2
deterministic core), `QaoaValue.qaoa_value_degree_bound` and
`QaoaValue.qaoa_value_tendsto_one_half` (c002, Theorem 4.2
degree-asymptotic core), and
`NeighborhoodGrowth.geometric_growth`/`depth_cap_bounds_growth`
(c008, Lemma 4.7 depth-cap core).

The remaining claims are recorded as abstract statements:
- c001 (Theorem 4.1): the transfer of the D-regular tree formula to
  Erdős–Rényi instances valid up to depth `ε log n`; needs the
  random-hypergraph moment recursion and the w.h.p. local-convergence
  machinery.
- c003 (Corollary 4.2.1): the `p → ∞` limit bound against the Parisi
  value `Π_q`; needs the infinite-depth limit and the Parisi constant.
- c005 (Lemma 4.4): the edge-removal bound `n·O_λ(1/λ^{c log λ})`;
  needs first/second moment analysis on the Erdős–Rényi hypergraph.
- c006/c007 (Lemmas 4.5/4.6): the w.h.p. treelike-fraction statements;
  need cycle-count concentration (Poisson small-subgraph counts).
- c009 (Corollary 1.2.1): the no-advantage conclusion; needs the
  QAOA-as-local-algorithm equivalence of the cited references.

-/
set_option autoImplicit false

open Filter Topology

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

/-! ## Claim statements -/

/-- **c001 (Theorem 4.1), transfer shape**: evaluating the QAOA value by
the D-regular girth-`> 2p+1` tree formula (`formula n p`) is valid for
the Erdős–Rényi instance (`eval n p`) at all depths `p ≤ ε log n`, for
some `ε > 0` — the algorithmic-limit theorem that Theorem 4.2's proof
reduces to. The instance ensemble, the w.h.p. probability and the
moment recursion are abstracted away. -/
def c001_statement (eval formula : ℕ → ℕ → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ n p : ℕ, (p : ℝ) ≤ ε * Real.log n → eval n p = formula n p

/-- **c003 (Corollary 4.2.1), limit shape**: the infinite-depth QAOA
value sequence is bounded by the OGP level `ηOGP`, which is strictly
below the Parisi value `Π_q` of the pure q-spin glass. The Parisi
constant and the `p → ∞` limit are abstracted away. -/
def c003_statement (value : ℕ → ℝ) (ηOGP parisi : ℝ) : Prop :=
  (∀ p : ℕ, value p ≤ ηOGP) ∧ ηOGP < parisi

/-- **c005 (Lemma 4.4), edge-removal shape**: with average degree
`λ > 1`, constants `c, C > 0`, the number of edges removed when
regularising the Erdős–Rényi hypergraph on `n` vertices is at most
`n · C / λ^{c log λ}`. The first-moment analysis of the removal
process is abstracted away. -/
def c005_statement (removed : ℕ → ℝ) (rate c C : ℝ) : Prop :=
  1 < rate ∧ 0 < c ∧ 0 < C ∧
    ∀ n : ℕ, removed n ≤ n * C / rate ^ (c * Real.log rate)

/-- **c006/c007 (Lemmas 4.5/4.6), treelike-fraction shape**: the
fraction of `l`-local neighbourhoods that are treelike (for `l ≤ ε log n`,
before and after edge addition) is a `[0,1]`-valued quantity tending
to `1` as `n → ∞`. The cycle-count concentration behind the statement
is abstracted away. -/
def c006_statement (frac : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ frac n ∧ frac n ≤ 1) ∧ Filter.Tendsto frac Filter.atTop (𝓝 1)

/-- **c009 (Corollary 1.2.1), no-advantage shape**: the QAOA optimised
by the cited parameter-selection algorithm performs no better than the
best local classical algorithm. The QAOA-as-local-algorithm equivalence
is abstracted away. -/
def c009_statement (qaoa localClassical : ℝ) : Prop :=
  qaoa ≤ localClassical

end Qatlib.Papers.OGPQAOAGoh25.MainResults
