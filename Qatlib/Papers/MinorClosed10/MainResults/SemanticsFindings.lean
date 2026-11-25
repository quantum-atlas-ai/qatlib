/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

/-! # Semantic findings for subgraph and minor closure

Childs--Kothari, arXiv:1011.1443v2, Section 2 (p. 4) and Corollary 2.1 (p. 5).

Two source-level points are settled here.

* The paper's subgraph relation deletes edges *and isolated vertices*, while the
  locked `SubgraphClosed` only deletes edges on a fixed vertex set.  The
  vertex-deleting closure `SubgraphClosedDel` is introduced, its relation to
  `SubgraphClosed` is proved, and a concrete property separating the two is
  exhibited.
* Under the locked minor model, the property "the vertex set is nonempty" is
  minor closed but has no finite forbidden-topological-minor description.
  This is a counterexample to Corollary 2.1 for the locked semantics; it is
  recorded as a scope finding, not as a proof of the paper's corollary.
-/

set_option autoImplicit false
namespace Qatlib.Papers.MinorClosed10.MainResults.SemanticsFindings

open Qatlib.Papers.MinorClosed10.MainResults
open Filter

/-! ## Subgraph closure with vertex deletion -/

/-- `P` is closed under taking subgraphs in the paper's sense (Section 2, p. 4):
deleting edges and isolated vertices preserves `P`.  Unlike `SubgraphClosed`,
the target graph may have a different number of vertices. -/
def SubgraphClosedDel (P : GraphProperty) : Prop :=
  ∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)),
    P (Fin n) G → ContainsSubgraph H G → P (Fin m) H

/-- The empty graph is a subgraph of any graph on the same vertex set. -/
theorem bot_containsSubgraph {m : ℕ} (G : SimpleGraph (Fin m)) :
    ContainsSubgraph (⊥ : SimpleGraph (Fin m)) G :=
  ⟨Function.Embedding.refl (Fin m),
    fun _ _ h => (SimpleGraph.bot_adj _ _).mp h |>.elim⟩

/-- A graph with a fixed vertex set is a subgraph of itself. -/
theorem containsSubgraph_of_le {n : ℕ} {H G : SimpleGraph (Fin n)} (h : H ≤ G) :
    ContainsSubgraph H G :=
  ⟨Function.Embedding.refl (Fin n), fun _ _ hab => h hab⟩

/-- Part (ii) of the card: vertex-deleting subgraph closure implies the locked
fixed-vertex-set closure. -/
theorem subgraphClosed_of_subgraphClosedDel {P : GraphProperty}
    (h : SubgraphClosedDel P) : SubgraphClosed P := by
  intro n G H hG hHG
  exact h n n G H hG (containsSubgraph_of_le hHG)

/-- The property "the graph is not complete".  It is preserved by deleting
edges, which is why it is subgraph closed on a fixed vertex set. -/
def NotCompleteProperty : GraphProperty :=
  fun _ _ _ G => G ≠ ⊤

/-- `NotCompleteProperty` is closed under edge deletion. -/
theorem notComplete_subgraphClosed : SubgraphClosed NotCompleteProperty := by
  intro n G H hG hHG hH
  apply hG
  have hGH : (⊤ : SimpleGraph (Fin n)) ≤ G := by
    rw [hH] at hHG
    exact hHG
  exact top_le_iff.mp hGH

/-- The complete graph on the first two vertices of `Fin 3`, leaving the third
vertex isolated.  It is not complete, but it contains an edge. -/
def twoVertexCompleteWithIsolate : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun a b : Fin 3 => a.val < 2 ∧ b.val < 2)

/-- The three-vertex example is not the complete graph. -/
theorem twoVertexCompleteWithIsolate_not_top :
    twoVertexCompleteWithIsolate ≠ (⊤ : SimpleGraph (Fin 3)) := by
  intro h
  have hnadj : ¬ twoVertexCompleteWithIsolate.Adj 0 2 := by
    simp [twoVertexCompleteWithIsolate, SimpleGraph.fromRel_adj]
  rw [h] at hnadj
  exact hnadj (by simp)

/-- It contains the complete graph on two vertices as a subgraph. -/
theorem twoVertexComplete_containsSubgraph :
    ContainsSubgraph (⊤ : SimpleGraph (Fin 2)) twoVertexCompleteWithIsolate := by
  refine ⟨⟨Fin.castLE (by norm_num), Fin.castLE_injective _⟩, ?_⟩
  intro a b hab
  have hne : a ≠ b := (SimpleGraph.top_adj a b).mp hab
  have hcne : Fin.castLE (by norm_num : 2 ≤ 3) a ≠
      Fin.castLE (by norm_num : 2 ≤ 3) b :=
    fun he => hne (Fin.castLE_injective _ he)
  have hlt : ∀ x : Fin 2, (Fin.castLE (by norm_num : 2 ≤ 3) x).val < 2 := by
    intro x
    fin_cases x <;> norm_num
  rw [twoVertexCompleteWithIsolate, SimpleGraph.fromRel_adj]
  exact ⟨hcne, Or.inl ⟨hlt a, hlt b⟩⟩

/-- Part (iii) of the card: `SubgraphClosed` does not imply
`SubgraphClosedDel`; deleting the isolated third vertex of the example produces
a complete graph, which the property rejects. -/
theorem not_subgraphClosedDel_notComplete :
    ¬ SubgraphClosedDel NotCompleteProperty := by
  intro h
  have hbad : NotCompleteProperty (Fin 2) (⊤ : SimpleGraph (Fin 2)) := by
    exact h 3 2 twoVertexCompleteWithIsolate ⊤
      twoVertexCompleteWithIsolate_not_top twoVertexComplete_containsSubgraph
  exact hbad rfl

/-- Part (iv) of the card: a nontrivial vertex-deleting subgraph-closed property
contains the empty graph for all sufficiently large vertex counts. -/
theorem empty_mem_of_nontrivial {P : GraphProperty} (hnt : IsNontrivial P)
    (hcl : SubgraphClosedDel P) :
    ∀ᶠ n in atTop, P (Fin n) (⊥ : SimpleGraph (Fin n)) := by
  filter_upwards [hnt] with n hn
  obtain ⟨G, hG⟩ := hn.1
  exact hcl n n G ⊥ hG (bot_containsSubgraph G)

/-! ## The nonempty-vertex property and Corollary 2.1 -/

/-- The property "the vertex set is nonempty". -/
def NonemptyVertexProperty : GraphProperty :=
  fun V _ _ _ => Nonempty V

/-- Under the locked minor model (a surjective map from the host vertices onto
the pattern vertices with connected fibres), a nonempty host forces a nonempty
pattern.  Hence the nonempty-vertex property is minor closed. -/
theorem nonemptyVertex_minorClosed : MinorClosed NonemptyVertexProperty := by
  intro m n H G hG hminor
  obtain ⟨f, _, _⟩ := hminor
  obtain ⟨v⟩ := hG
  exact ⟨f v⟩

/-- Every graph contains the empty graph as a topological minor. -/
theorem empty_containsTopologicalMinor {W : Type} (G : SimpleGraph W) :
    ContainsTopologicalMinor (⊥ : SimpleGraph (Fin 0)) G := by
  refine ⟨⟨fun i => i.elim0, ?_⟩, (fun a => a.elim0), ?_, ?_⟩
  · intro a
    exact a.elim0
  · intro a
    exact a.elim0
  · intro a
    exact a.elim0

/-- A walk of length one has no interior vertices. -/
theorem walkInterior_cons_nil {V : Type} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) :
    WalkInterior (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) = ∅ := by
  ext x
  simp [WalkInterior, SimpleGraph.Walk.support_cons]
  tauto

/-- Every graph on at most `n` vertices is a topological minor of the complete
graph on `Fin n`: embed the vertices and use the direct edge for every edge of
the pattern. -/
theorem complete_containsTopologicalMinor {m n : ℕ} (H : SimpleGraph (Fin m))
    (hmn : m ≤ n) :
    ContainsTopologicalMinor H (⊤ : SimpleGraph (Fin n)) := by
  refine ⟨⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩, ?_, ?_, ?_⟩
  · intro a b hab
    have hne : (Fin.castLE hmn a) ≠ (Fin.castLE hmn b) := by
      intro he
      exact H.ne_of_adj hab (Fin.castLE_injective hmn he)
    exact SimpleGraph.Walk.cons (by simpa [SimpleGraph.top_adj] using hne)
      SimpleGraph.Walk.nil
  · intro a b hab x hx
    rw [walkInterior_cons_nil] at hx
    exact hx.elim
  · intro a b hab c d hcd x hxy hx hy
    rw [walkInterior_cons_nil] at hx
    exact hx.elim

/-- **Corollary 2.1 fails for the locked minor semantics.**  The nonempty-vertex
property is minor closed, but no finite set of forbidden topological minors
describes it: the empty graph is a topological minor of every graph, while the
property is false on the empty vertex set; when a forbidden graph with vertices
is present, a sufficiently large complete graph contains it. -/
theorem nonemptyVertex_not_described :
    ¬ DescribedByForbiddenTopologicalMinors NonemptyVertexProperty := by
  rintro ⟨F, hF⟩
  by_cases hFempty : F = ∅
  · have hR : ∀ f ∈ F, ¬ ContainsTopologicalMinor f.2
        (⊥ : SimpleGraph (Fin 0)) := by
      simp [hFempty]
    have hP : NonemptyVertexProperty (Fin 0) (⊥ : SimpleGraph (Fin 0)) :=
      (hF (Fin 0) (⊥ : SimpleGraph (Fin 0))).mpr hR
    exact hP.elim (fun x => x.elim0)
  · obtain ⟨f₀, hf₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
    let n : ℕ := F.sup (fun f : Sigma fun k : ℕ => SimpleGraph (Fin k) => f.1) + 1
    have hn : 0 < n := Nat.succ_pos _
    have hcont : ∀ f ∈ F, ContainsTopologicalMinor f.2
        (⊤ : SimpleGraph (Fin n)) := by
      intro f hf
      refine complete_containsTopologicalMinor f.2 ?_
      have hle : f.1 ≤ F.sup
          (fun f : Sigma fun k : ℕ => SimpleGraph (Fin k) => f.1) :=
        Finset.le_sup (s := F) (f := fun f : Sigma fun k : ℕ =>
          SimpleGraph (Fin k) => f.1) hf
      dsimp [n]
      omega
    have hP : NonemptyVertexProperty (Fin n) (⊤ : SimpleGraph (Fin n)) :=
      ⟨⟨0, hn⟩⟩
    have hR := (hF (Fin n) (⊤ : SimpleGraph (Fin n))).mp hP
    exact hR f₀ hf₀ (hcont f₀ hf₀)

end Qatlib.Papers.MinorClosed10.MainResults.SemanticsFindings
