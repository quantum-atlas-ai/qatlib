/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 2: injectivity of the parity map `f` and girth (paper p.6)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Lemma 2, Section 2.1, p.6.

The paper's map `f : {0,1}^E → {0,1}^V` sends a subgraph `β` to the parity vector of its vertex
degrees, `f(β)_v = Σ_{e ∋ v} β_e (mod 2)`. Lemma 2 states:

> Suppose we have a graph `G` and `l ∈ ℕ`. Then `f` is injective on `ℰ_l` if and only if `G` has
> girth at least `2l + 1`.

The proposition is recorded as `lemma2_parityMap_injective_iff_egirth` below. The paper's "girth at
least `2l+1`" is read with the extended girth `SimpleGraph.egirth : ℕ∞`, since a forest has
infinite girth (whereas Mathlib's junk-valued `SimpleGraph.girth : ℕ` is `0` on forests).

**Formalisation status.** The statement is recorded as a `def : Prop`, not as a proved theorem:
both directions are currently a substantive formalisation gap (see the docstring of the `def`).
No unproved placeholder is used. Theorem 1 takes the injectivity instance as an explicit hypothesis instead.
-/

open scoped BigOperators
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Lemma2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 2** (Parekh, arXiv:2509.19966v2, Lemma 2, p.6): for a graph `G` and `l ∈ ℕ`, the
parity map `f` is injective on `ℰ_l = {β ∈ {0,1}^E | |β| ≤ l}` if and only if `G` has girth at
least `2l + 1` (extended girth: infinite for forests).

**Paper proof, both directions** (p.6–7):
* (⇐) If `f(β) = f(β')` with `β ≠ β'`, the symmetric difference `γ = β + β'` is a nonempty
  subgraph with even degree at every vertex and `|γ| ≤ 2l`. Every nonempty finite graph with all
  degrees even contains a cycle; that cycle has length `≤ |γ| ≤ 2l`, contradicting girth
  `≥ 2l + 1`.
* (⇒) If `G` contains a cycle of length `c ≤ 2l`, split it into two edge-disjoint paths of
  length `≤ l` between the same two vertices; their incidence vectors `β, β' ∈ ℰ_l` are distinct
  but have equal parity vector.

**Lean gap (substantive).** Neither direction is currently proved. The missing ingredients are:
* a formal "even-degree nonempty subgraph contains a cycle" lemma. Mathlib provides leaf
  existence for trees (`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`) but not the
  degree-parity bridge from `incMatrix *ᵥ edgeVec` to the degree of `fromEdgeSet β`;
* the walk-splitting construction using `SimpleGraph.Walk.take` / `SimpleGraph.Walk.drop`
  (`Mathlib.Combinatorics.SimpleGraph.Walk.Operations`) plus `Walk.length`, `Walk.edges`, and a
  proof that the parity vector of a path is its endpoint indicator.

Recorded as a `def : Prop` (no proof, no placeholder) for reuse by restricted downstream statements.

**Candidate reusable dependencies.** `SimpleGraph.Walk.take`, `SimpleGraph.Walk.drop`,
`SimpleGraph.Walk.length`, `SimpleGraph.Walk.edges`, `SimpleGraph.Walk.rotate`,
`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`,
`SimpleGraph.egirth_le_length` / `SimpleGraph.three_le_girth`,
`SimpleGraph.incMatrix_apply'`, `SimpleGraph.card_incidenceSet_eq_degree`,
`Finset.sum_boole`.

**Suggested takeover tactics.** (⇐) Let `γ = β \ β' ∪ β' \ β` (`Finset.symmDiff`), use
`incMatrix` linearity over `ZMod 2` (`Matrix.mulVec_add`, `ZMod 2` arith) to get `f(γ) = 0` with
`0 < γ.card ≤ 2*l`, build `H = SimpleGraph.fromEdgeSet γ`, show every `H.degree v` is even, and
contradict `H.IsAcyclic` using a leaf of a nontrivial tree component; (⇒) from
`SimpleGraph.exists_egirth_eq_length` take a cycle `c` with `c.length ≤ 2*l` and split it at the
midpoint with `Walk.take`/`Walk.drop` into two distinct `ℰ_l` elements with equal parity. -/
def lemma2_parityMap_injective_iff_egirth
    (G : SimpleGraph V) [DecidableRel G.Adj] (l : ℕ) : Prop :=
  Function.Injective (parityMap G l) ↔ (2 * l + 1 : ℕ∞) ≤ G.egirth

end Lemma2

end Qatlib.Papers.DQIAdvantage25.MainResults
