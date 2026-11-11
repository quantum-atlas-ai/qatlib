/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Clique complex and Betti numbers — Lemma 4.1 core

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11).

We build the concrete combinatorial model used in Section 4: for a finite simple graph `G` on
`V`, the `d`-simplices of the clique (flag) complex `X(G)` are the `(d+1)`-cliques (`simplices`),
the real chains are finitely supported functions on vertex sets, and `bettiNumber G d` is the
dimension of the space of real `d`-cycles. Over a `d`-skeleton (`∂_{d+1} = 0`) this is exactly
the paper's Eq. (5), `β_d = dim ker ∂_d`.

Main results here:

* `simplices_eq_empty_of_cliqueFree`: a `(k-1)`-clique-free graph has no `(k-2)`-simplex.
* `bettiNumber_eq_zero_of_simplices_eq_empty`: `f_d = 0 ⇒ β_d = 0`.
* `lemma_4_1_core`: **Lemma 4.1 (Null value), deterministic core** — a graph with no
  `(k-1)`-clique has `β_{k-2} = 0`; fully proved.

The probabilistic half of Lemma 4.1 (the Markov bound on the expected number of
`(k-1)`-cliques in `G(n, 1/2)`, p.10) and Lemma 4.2's boundary-sphere cycle are stated
separately with the paper's arguments documented.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Topology

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `d`-simplices of the clique complex `X(G)` of `G`: the vertex sets of cardinality `d+1`
that are cliques (pairwise adjacent). These are exactly the clique-complex `d`-simplices of
the paper (§3.1, p.7). -/
def simplices (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun σ : Finset V => σ.card = d + 1 ∧ G.IsClique σ)

/-- `f_d(G)`, the number of `d`-simplices of `X(G)` (paper Eq. (1)). -/
def numSimplices (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (simplices G d).card

/-- A vertex set is a `d`-simplex of the clique complex iff it has `d+1`
vertices and is a clique. -/
lemma mem_simplices_iff (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (σ : Finset V) :
    σ ∈ simplices G d ↔ σ.card = d + 1 ∧ G.IsClique σ := by
  simp [simplices]

section Oriented

variable [LinearOrder V]

/-- The oriented boundary of a vertex set `σ`, viewed as one summand in a chain: the alternating
sum, over the vertices of `σ`, of the facet `σ.erase v`, with the sign `(-1)` powered by the
position of `v` in the sorted order. This is the standard simplicial boundary operator
(Section 3.1, p.8). -/
def simplexBoundary (σ : Finset V) : (Finset V) →₀ ℝ :=
  ((σ.sort (· ≤ ·)).zipIdx.map
    (fun p : V × ℕ => Finsupp.single (σ.erase p.1) ((-1 : ℝ) ^ p.2))).sum

/-- The boundary operator `∂` on real chains (finite supports of vertex sets). -/
def boundaryMap : ((Finset V) →₀ ℝ) →ₗ[ℝ] ((Finset V) →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun σ : Finset V => simplexBoundary σ)

/-- The real `d`-cycle space of the `d`-skeleton of the clique complex: chains spanned by
`d`-simplices whose boundary vanishes. -/
def cycleSpace (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    Submodule ℝ ((Finset V) →₀ ℝ) :=
  Submodule.span ℝ
      ((↑(simplices G d) : Set (Finset V)).image (fun σ => Finsupp.single σ (1 : ℝ)))
    ⊓ LinearMap.ker boundaryMap

/-- The Betti number `β_d(skel_d X(G))` of the `d`-skeleton, formula (5) of the paper with the
filling term `∂_{d+1} = 0`: the dimension of the space of real `d`-cycles. -/
def bettiNumber (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  Module.finrank ℝ (cycleSpace G d)

/-! ### Lemma 4.1 — the deterministic core -/

/-- A graph with no `(k-1)`-clique has no `(k-2)`-simplex in its clique complex. -/
theorem simplices_eq_empty_of_cliqueFree (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k) (h : G.CliqueFree (k - 1)) : simplices G (k - 2) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  rw [mem_simplices_iff] at hσ
  obtain ⟨hcard, hcl⟩ := hσ
  exact h σ ⟨hcl, by omega⟩

/-- If there are no `d`-simplices then the `d`-cycle space is trivial, so `β_d = 0`. -/
theorem bettiNumber_eq_zero_of_simplices_eq_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (h : simplices G d = ∅) : bettiNumber G d = 0 := by
  unfold bettiNumber cycleSpace
  have hspan :
      Submodule.span ℝ
        ((↑(simplices G d) : Set (Finset V)).image (fun σ => Finsupp.single σ (1 : ℝ)))
        = ⊥ := by
    rw [h]; simp
  rw [hspan, bot_inf_eq]
  exact finrank_bot ℝ ((Finset V) →₀ ℝ)

/-- **Lemma 4.1 (Null value), deterministic core** (§4, p.10). If `G₀` has no `(k-1)`-clique
then `β_{k-2}(skel_{k-2} X(G₀)) = 0`. The full statement additionally shows `G₀ ∼ G(n,1/2)`
is w.h.p. `(k-1)`-clique-free (Markov on the expected count of `(k-1)`-cliques,
`E ≤ n^{k-1} 2^{-(k-2)/2} = n^{-ε/2+o(1)} → 0`, p.10). That probabilistic half is not
formalised here (no Erdős–Rényi probability space in the library); this theorem is the
deterministic implication `clique-free ⇒ β_{k-2}=0` that it feeds. -/
theorem lemma_4_1_core (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (h : G.CliqueFree (k - 1)) : bettiNumber G (k - 2) = 0 :=
  bettiNumber_eq_zero_of_simplices_eq_empty G
    (simplices_eq_empty_of_cliqueFree G hk h)

end Oriented

end Qatlib.Papers.BettiHardness26.MainResults.Topology
