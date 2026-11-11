/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel
import Qatlib.Papers.DQIAdvantage25.MainResults.Lemma5TreePartition

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3: bounded cycle rank for connected high-girth graphs (paper p.10)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Theorem 3, Section 3, p.10.

> **Theorem 3.** For a connected graph `G ∈ 𝒢` with girth `g = Ω(m)`, the quantity
> `μ = m - n + 1` is constant.

**Paper proof** (p.10). Take a spanning tree `T` and the partition `T_1, …, T_t` of Lemma 5.
Every edge of `G - T` joins distinct `T_i`, and Lemma 5(ii) allows at most one such edge per pair,
so `G - T` has at most `t(t-1)/2 = O(1)` edges. Since `μ = |G - T| = m - n + 1`, `μ` is constant
(bounded by a constant independent of `G`, depending only on the implicit constant in `g = Ω(m)`).

`cycleRank` in `Model/CutGirthModel.lean` is `μ = m - n + 1`, an integer because `m - n + 1` can
be `0` for a tree. The `O(1)` is made explicit as a bound `C : ℤ` depending only on `c`.
-/

open scoped BigOperators
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Theorem3

/-- **Theorem 3** (Parekh, arXiv:2509.19966v2, Theorem 3, p.10). For every constant `c > 0` there
is a bound `C` such that every connected graph with girth `g ≥ c·m` has cycle rank
`μ = m - n + 1 ≤ C`; i.e. `μ` is bounded by a constant independent of the graph.

**Lean gap (substantive).** The statement is faithful; the proof is not formalised. It combines
`Lemma5.lemma5_tree_partition` with:
* `SimpleGraph.Connected.exists_spanningTree`-type existence and `IsTree.card_edgeFinset`
  (`= n - 1`) to identify `μ = m - n + 1` with the number of non-tree edges;
* the counting bound `#(G - T) ≤ t(t-1)/2 ≤ C(C-1)/2` from at most one inter-part edge per pair.
Both the tree-partition input and the edge-partition counting are substantial Finset/graph
bookkeeping.

Recorded as a `def : Prop` (no proof, no placeholder) so that Corollary 1 can cite it as an explicit
hypothesis in a restricted statement.

**Candidate reusable dependencies.** `Lemma5.lemma5_tree_partition`,
`SimpleGraph.exists_spanningTree`, `SimpleGraph.IsTree.card_edgeFinset`,
`Finset.card_sdiff` / `Finset.card_filter`, `Set.Subsingleton`,
`Finset.card_le_card`, `Nat.choose_two_right`.

**Suggested takeover tactics.** Obtain `C` from `lemma5_tree_partition c hc`, fix a spanning tree
`T` (`exists_spanningTree`), compute `μ = |E(G) \ E(T)|` with
`Finset.card_sdiff` + `IsTree.card_edgeFinset`, then bound `|E(G) \ E(T)| ≤ C.choose 2` by
injecting each non-tree edge into the unordered pair of parts it joins (well defined by
`Subsingleton`); finish with `omega` on the integer identity `μ = m - n + 1`. -/
def theorem3_cycleRank_bounded (c : ℝ) (_hc : 0 < c) : Prop :=
  ∃ C : ℤ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → c * (numEdges G : ℝ) ≤ (G.girth : ℝ) → cycleRank G ≤ C

end Theorem3

end Qatlib.Papers.DQIAdvantage25.MainResults
