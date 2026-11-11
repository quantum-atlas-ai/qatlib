/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card

set_option backward.isDefEq.respectTransparency false

/-!
# Graph/binary-string encoding (Gaitan--Clark, arXiv:1103.1345v3)

Fixed source: arXiv:1103.1345v3 (8 Jan 2012), page 2, Eq. (1).

The paper establishes a 1-1 correspondence between `N`-vertex graphs and binary
strings of length `L = N(N-1)/2` by writing down the lower triangular part of
the adjacency matrix column-wise (Eq. (1)).  Each bit is identified with a
vertex pair `(i,j)`, and the adiabatic register uses one qubit per bit, hence
`L = N(N-1)/2` qubits.

This file proves the mathematical content of that statement:

* `card_simpleGraph_fin`: there are exactly `2^(N.choose 2)` simple graphs on
  `Fin N`,
* `graph_encoding_equiv`: a bijection between `SimpleGraph (Fin N)` and
  `Fin (N.choose 2) → Bool`,
* `qubitCount_eq`: `N.choose 2 = N*(N-1)/2`.

The bijection is obtained from the edge-set description: a simple graph is
exactly a subset of the off-diagonal unordered vertex pairs (`Sym2`), and there
are `C(N,2)` such pairs.  This is the Lean counterpart of Eq. (1).
-/

set_option autoImplicit false

namespace Qatlib.Papers.RamseyAdiab11.MainResults.Encoding

open Finset

variable {V : Type*}

/-- Inverse direction of Eq. (1): the graph whose edge set is a given
off-diagonal set of unordered pairs. -/
def graphOfEdgeFinset [DecidableEq V] (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) : SimpleGraph V where
  Adj u v := s(u, v) ∈ E
  symm := ⟨fun u v huv => by
    change s(v, u) ∈ E
    rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun v hv => hE s(v, v) hv (Sym2.mk_isDiag_iff.mpr rfl)⟩

/-- Definitional unfolding of `graphOfEdgeFinset`: the adjacency relation is
membership in the prescribed edge set. -/
theorem graphOfEdgeFinset_adj [DecidableEq V] (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (u v : V) :
    (graphOfEdgeFinset E hE).Adj u v ↔ s(u, v) ∈ E :=
  Iff.rfl

/-- The edge set of `graphOfEdgeFinset E` is exactly `E`. -/
theorem graphOfEdgeFinset_edgeFinset [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    [Fintype (Sym2 V)] [DecidableRel (graphOfEdgeFinset E hE).Adj] :
    (graphOfEdgeFinset E hE).edgeFinset = E := by
  apply Finset.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro u v
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graphOfEdgeFinset_adj]

/-- Paper Eq. (1), page 2: a graph is determined by its set of edges, viewed as
a subset of the off-diagonal unordered vertex pairs. -/
noncomputable def graphEdgeEquiv [Fintype V] [DecidableEq V] :
    SimpleGraph V ≃ {E : Finset (Sym2 V) // ∀ e ∈ E, ¬ e.IsDiag} := by
  classical
  haveI : Fintype (Sym2 V) := Fintype.ofFinite _
  exact
    { toFun := fun G => ⟨G.edgeFinset, fun e he => G.not_isDiag_of_mem_edgeFinset he⟩
      invFun := fun E => graphOfEdgeFinset E.1 E.2
      left_inv := fun G => by
        ext u v
        show s(u, v) ∈ (G.edgeFinset : Finset (Sym2 V)) ↔ G.Adj u v
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      right_inv := fun E => by
        apply Subtype.ext
        exact graphOfEdgeFinset_edgeFinset E.1 E.2 }

/-- The number of off-diagonal edge subsets of `Fin N` is `2^{C(N,2)}`, because
the off-diagonal unordered pairs number `C(N,2)` (`Sym2.card_subtype_not_diag`). -/
theorem card_offdiagFinset (N : ℕ) :
    Fintype.card {E : Finset (Sym2 (Fin N)) // ∀ e ∈ E, ¬ e.IsDiag} =
      2 ^ (N.choose 2) := by
  classical
  let S : Finset (Sym2 (Fin N)) := Finset.univ.filter (fun e => ¬ e.IsDiag)
  have hmem : ∀ E : Finset (Sym2 (Fin N)), E ∈ S.powerset ↔ ∀ e ∈ E, ¬ e.IsDiag := by
    intro E
    simp [Finset.mem_powerset, Finset.subset_iff, S]
  have hcard := Fintype.card_of_subtype S.powerset hmem
  rw [hcard, Finset.card_powerset]
  have hS : S.card = N.choose 2 := by
    have hsub : Fintype.card {e : Sym2 (Fin N) // ¬ e.IsDiag} = S.card :=
      Fintype.card_of_subtype S (fun e => by simp [S])
    rw [← hsub]
    simpa using (Sym2.card_subtype_not_diag (α := Fin N))
  rw [hS]

/-- Paper page 2, Eq. (1) and the following paragraph: there are exactly
`2^{N(N-1)/2}` simple graphs on `N` vertices. -/
theorem card_simpleGraph_fin (N : ℕ) :
    Fintype.card (SimpleGraph (Fin N)) = 2 ^ (N.choose 2) := by
  classical
  rw [Fintype.card_congr (graphEdgeEquiv (V := Fin N)), card_offdiagFinset]

/-- Paper page 2: the binary string `g(G)` of Eq. (1) has length `L = N(N-1)/2`;
equivalently `C(N,2)` and `N*(N-1)/2` agree. -/
theorem qubitCount_eq (N : ℕ) : N.choose 2 = N * (N - 1) / 2 :=
  Nat.choose_two_right N

/-- Paper Eq. (1): a 1-1 correspondence between `N`-vertex graphs and binary
strings of length `L = C(N,2)`, i.e. an explicit bijection with `Bool`-valued
functions on `Fin (N.choose 2)`. -/
theorem graph_encoding_equiv (N : ℕ) :
    Nonempty (SimpleGraph (Fin N) ≃ (Fin (N.choose 2) → Bool)) := by
  classical
  have hcard : Fintype.card (SimpleGraph (Fin N)) =
      Fintype.card (Fin (N.choose 2) → Bool) := by
    rw [card_simpleGraph_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact ⟨Fintype.equivOfCardEq hcard⟩

end Qatlib.Papers.RamseyAdiab11.MainResults.Encoding
