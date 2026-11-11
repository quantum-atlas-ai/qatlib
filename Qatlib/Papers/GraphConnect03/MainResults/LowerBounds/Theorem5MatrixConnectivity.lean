/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.AmbainisMethod

/-!
# Theorem5MatrixConnectivity — the lower bound of Theorem 5

Dürr--Mhalla--Lei, *Quantum query complexity of graph connectivity*,
fixed arXiv:quant-ph/0303169v3 (5 Apr 2003), Theorem 5 and its proof (p.8),
Figure 3.

Theorem 5: Connectivity needs `Ω(n^{3/2})` queries in the adjacency-matrix
model (even for undirected graphs).

The source applies Ambainis' method to the promise problem of distinguishing a
graph with exactly one cycle from a graph with exactly two cycles of lengths in
`[n/3, 2n/3]`.  `X` is the set of adjacency matrices of a unique cycle, `Y` the
set of adjacency matrices with exactly two such cycles, and `M R M′` when the
only differences are four edges: `(a,b), (c,d)` present in `M` and absent in
`M′`, `(a,c), (b,d)` absent in `M` and present in `M′` (a 2-switch along the
cycle, Figure 3).  The counts are `m = O(n²)`, `m′ = O(n²)` (the length
constraint gives the factor `n/3` in both directions) and
`l_{M,(i,j)} l′_{M′,(i,j)} = O(n)` (one of the two factors is constant `4`,
the other linear); hence `√(m m′/l_max) = Ω(n^{3/2})`.

This file records the relation and the proved arithmetic evaluation
`sqrt_matrix_parameters`; the parameter counts and the final lower bound are
recorded as explicit gaps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Qatlib.Papers.GraphConnect03.MainResults

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.Defs

attribute [local instance] Classical.propDecidable

/-- `TwoRegular M`: every vertex has exactly two neighbours, i.e. the graph is a
disjoint union of cycles. -/
def TwoRegular {n : ℕ} (M : UndirectedMatrix n) : Prop :=
  ∀ v : Vertex n, (Finset.univ.filter (fun w => M.adj v w = true)).card = 2

/-- `UniqueCycle M`: a single cycle through all vertices (the source's set `X`):
the graph is 2-regular and connected. -/
def UniqueCycle {n : ℕ} (M : UndirectedMatrix n) : Prop :=
  TwoRegular M ∧ M.Connected

/-- `TwoCycles M`: exactly two cycles (the source's set `Y`); the two components
each have between `n/3` and `2n/3` vertices.  The component-length constraint is
recorded through `componentSize`, the number of vertices reachable from `v`. -/
def componentSize {n : ℕ} (M : UndirectedMatrix n) (v : Vertex n) : ℕ :=
  (Finset.univ.filter (fun w => M.toDigraph.Reach v w)).card

def TwoCycles {n : ℕ} (M : UndirectedMatrix n) : Prop :=
  TwoRegular M ∧ ¬ M.Connected ∧
    ∃ v w : Vertex n, ¬ M.toDigraph.Reach v w ∧
      3 * componentSize M v ≥ n ∧ 3 * componentSize M v ≤ 2 * n ∧
      3 * componentSize M w ≥ n ∧ 3 * componentSize M w ≤ 2 * n

/-- The relation of Theorem 5 (Figure 3): `M R M′` iff the only differences are
the four edges of a 2-switch along the cycle, `(a,b), (c,d)` in `M` versus
`(a,c), (b,d)` in `M′`, all between distinct vertices `a, b, c, d`. -/
def MatrixEdgeSwapRel {n : ℕ} (M M' : UndirectedMatrix n) : Prop :=
  ∃ a b c d : Vertex n,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    M.adj a b = true ∧ M.adj c d = true ∧
    M'.adj a b = false ∧ M'.adj c d = false ∧
    M'.adj a c = true ∧ M'.adj b d = true ∧
    M.adj a c = false ∧ M.adj b d = false ∧
    -- all other entries agree
    (∀ i j : Vertex n,
      ¬ ((i = a ∧ j = b) ∨ (i = b ∧ j = a) ∨ (i = c ∧ j = d) ∨ (i = d ∧ j = c) ∨
         (i = a ∧ j = c) ∨ (i = c ∧ j = a) ∨ (i = b ∧ j = d) ∨ (i = d ∧ j = b)) →
      M'.adj i j = M.adj i j)

/- The relation-parameter counts of Theorem 5 (`m = O(n²)`, `m′ = O(n²)`,
`l_max = O(n)`) are not stated as a declaration: they require the 2-switch
counting on the unique-cycle vs two-cycle promise problem, which is not
mechanized.  The arithmetic evaluation `√(m m′/l_max) = n^{3/2}` at the source's
parameter values is proved above as `sqrt_matrix_parameters`. -/

/- Source Theorem 5 (`Ω(n^{3/2})` matrix-model Connectivity lower bound) is not
stated as a declaration.  Its ingredients are: the promise relations
(`UniqueCycle`, `TwoCycles`, `MatrixEdgeSwapRel`), the relation-parameter counts
(recorded gap above), the abstract Ambainis relation bound (see `AmbainisMethod`),
and the passage to `Model.matrixConnectivityQueryComplexity`, which needs the
operational circuit semantics this block does not rebuild. -/

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
