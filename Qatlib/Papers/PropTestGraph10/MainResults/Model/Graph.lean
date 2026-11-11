/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: bounded-degree graphs

Fixed source: Ambainis--Childs--Liu, *Quantum property testing for bounded-degree
graphs*, arXiv:1012.3174v3 (20 Jun 2011). This module transcribes the paper's
Section 1 model (pp. 2--3) of a bounded-degree graph in the adjacency-list
representation, together with the three predicates used by the main results:
bipartiteness, `ε`-farness from a property, and the `α`-expander condition.

`BoundedDegreeGraph N d` is the paper's function `f_G : V × {1,…,d} → V ∪ {*}`;
the `none` value plays the role of `*`. No symmetry/consistency constraint is
imposed on the adjacency lists, matching the oracle model the paper analyses
(the paper treats `f_G` as an arbitrary oracle; structural promises are part of
the tested property, not of the model). `editDistance` counts changed adjacency
slots, exactly the paper's "change at least `ε n d` edges" (p. 3).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- A graph on `N` vertices with maximum degree `d`, stored as `d` adjacency-list
slots per vertex. The paper's representation `f_G : V × {1,…,d} → V ∪ {*}`
(p. 2), with `none` representing `*`. -/
structure BoundedDegreeGraph (N d : ℕ) where
  /-- Adjacency list: `adj v i` is the `i`-th neighbour of `v`, if present. -/
  adj : Fin N → Fin d → Option (Fin N)

/-- The finite set of all adjacency-list graphs (used by the sampling model). -/
instance instFintypeBoundedDegreeGraph {N d : ℕ} : Fintype (BoundedDegreeGraph N d) :=
  Fintype.ofInjective BoundedDegreeGraph.adj
    (fun G₁ G₂ h => by cases G₁; cases G₂; simpa using h)

/-- Bipartiteness: there is a two-colouring in which every stored edge joins
vertices of opposite colours. This is the property tested in Theorem 1 and
Theorem 10 (p. 3 and p. 15). -/
def IsBipartite {N d : ℕ} (G : BoundedDegreeGraph N d) : Prop :=
  ∃ color : Fin N → Bool,
    ∀ (v : Fin N) (i : Fin d) (w : Fin N), G.adj v i = some w → color v ≠ color w

/-- Number of adjacency-list slots in which two graphs differ. This is the edit
distance used by the paper's `ε`-farness definition ("change at least `ε n d`
edges of `G`", p. 3). -/
def editDistance {N d : ℕ} (G G' : BoundedDegreeGraph N d) : ℕ :=
  (by classical
    exact (Finset.univ.filter fun p : Fin N × Fin d => G.adj p.1 p.2 ≠ G'.adj p.1 p.2).card)

/-- `ε`-far from bipartite: every bipartite graph differs from `G` in at least
`ε N d` adjacency slots. This transcribes the paper's `ε`-far definition (p. 3)
specialised to the bipartiteness property. -/
def FarFromBipartite {N d : ℕ} (ε : ℝ) (G : BoundedDegreeGraph N d) : Prop :=
  ∀ G' : BoundedDegreeGraph N d,
    IsBipartite G' → ε * (N : ℝ) * (d : ℝ) ≤ (editDistance G G' : ℝ)

/-- The vertex boundary `∂(U)`: vertices outside `U` adjacent to at least one
vertex of `U` (p. 3). -/
def boundary {N d : ℕ} (G : BoundedDegreeGraph N d) (U : Finset (Fin N)) : Finset (Fin N) :=
  by classical
    exact Finset.univ.filter fun w =>
      w ∉ U ∧ ∃ v ∈ U, ∃ i : Fin d, G.adj v i = some w

/-- `α`-expander: for every `U` with `|U| ≤ |V|/2`, `|∂(U)| ≥ α |U|`. This is the
paper's definition on p. 3. -/
def IsExpander {N d : ℕ} (α : ℝ) (G : BoundedDegreeGraph N d) : Prop :=
  ∀ U : Finset (Fin N), 2 * U.card ≤ N → α * (U.card : ℝ) ≤ (boundary G U).card

/-- `ε`-far from every `α`-expander of degree at most `d`: every `α`-expander is
at edit distance at least `ε N d` from `G`. This is the rejection side of the
expansion-testing claims (Theorem 13, p. 16). -/
def FarFromExpanders {N d : ℕ} (ε α : ℝ) (G : BoundedDegreeGraph N d) : Prop :=
  ∀ G' : BoundedDegreeGraph N d,
    IsExpander α G' → ε * (N : ℝ) * (d : ℝ) ≤ (editDistance G G' : ℝ)

end Qatlib.Papers.PropTestGraph10.MainResults.Model
