/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SubgraphDet26.MainResults.GraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# Clique detection and clique collision (Theorems 1.1, 1.2; §4)

Paper: Gilani–Zhou, *Superlinear Quantum Query Lower Bounds for Subgraph Detection*,
fixed arXiv:2609.40263v1.

* Theorem 1.1, Eq. (1): the clique-detection exponent sequence `λ_r`;
* Theorem 1.2, Eq. (2): the clique-collision lower bound for `r`-partite graphs;
* Proposition 4.2, Eq. (45): partite graphs with unique clique extensions;
* Lemma 4.3, Eq. (46): overlaps between cliques;
* Proposition 4.4, Eq. (47): the graph-collision lower bound;
* Lemma 4.5, Eq. (48): reduction from graph collision to clique detection;
* Corollary 4.6, Eq. (49): the clique-detection exponent `1/2 + ℓ(2r−ℓ−1)/(2(r−1)(ℓ+1))`;
* Proposition 4.7, Eq. (50): the matching-number clique bound.

The lower bounds are stated through `QueryLowerBound` / `SearchLowerBound` of
`GraphModel.lean`; `n^{e-o(1)}` is encoded by `AsymptoticEdgeLowerBound` /
`AsymptoticMarkLowerBound` (`∀ ε > 0`, eventually `n^{e-ε}` queries are needed).

Theorem 1.1, Theorem 1.2, Proposition 4.2, Lemma 4.3, Proposition 4.4, Lemma 4.5,
Corollary 4.6 and Proposition 4.7 were removed: their proofs rest on the
certificate-search engine (Theorem 3.1 / Corollary 3.2), the probabilistic
construction of Proposition 4.2 and the OR-composition of Lemma 4.5, none of which
are available in the library; the statements are preserved in the branch history
at `161317a85`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Qatlib.Papers.SubgraphDet26.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix

/-! ## Auxiliary definitions from §4 -/

/-- The clique-collision exponent `ℓ(2r−ℓ+1) / (2r(ℓ+1))` of Eq. (2). -/
def cliqueCollisionExponent (r ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * (2 * (r : ℝ) - (ℓ : ℝ) + 1) / (2 * (r : ℝ) * ((ℓ : ℝ) + 1))

/-- The clique-detection exponent `1/2 + ℓ(2r−ℓ−1)/(2(r−1)(ℓ+1))` of Eq. (49). -/
def cliqueDetectionExponent (r ℓ : ℕ) : ℝ :=
  1 / 2 + (ℓ : ℝ) * (2 * (r : ℝ) - (ℓ : ℝ) - 1) /
    (2 * ((r : ℝ) - 1) * ((ℓ : ℝ) + 1))

/-- Ordered pairs of distinct members of `F` sharing exactly `j` vertices (Eq. (46)). -/
def orderedPairCount {n : ℕ} (F : Finset (Finset (Fin n))) (j : ℕ) : ℕ :=
  (F.product F).filter (fun p : Finset (Fin n) × Finset (Fin n) =>
    p.1 ≠ p.2 ∧ (p.1 ∩ p.2).card = j) |>.card

/-! ## Theorem 1.1 and Theorem 1.2 (main results) -/



/-! ## Proposition 4.2 and Lemma 4.3 -/



/-! ## Proposition 4.4, Lemma 4.5 and Corollary 4.6 -/




/-! ## Proposition 4.7 -/


end Qatlib.Papers.SubgraphDet26.MainResults
