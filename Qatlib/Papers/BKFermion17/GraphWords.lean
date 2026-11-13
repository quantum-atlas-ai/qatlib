/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import Mathlib.Tactic

/-!
# Graph-indexed Pauli words and support bounds

This module represents finite simple graphs by indexed, ordered endpoints and constructs their
vertex and edge Pauli words. The support of each word is controlled by incident edges, yielding
weight bounds in terms of graph degree. The associated matrices are Hermitian and unitary. See
[SetiaWhitfield2018].

## Main statements

* `vertex_support`: vertex support is exactly the incident edge set.
* `bounded_degree_support`: degree bounds control vertex and edge weights.
* `graph_generators`: the represented generators are Hermitian and unitary.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.BKFermion17.GraphWords
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
variable {M E : ℕ}

/-- A finite graph with indexed edges, strictly ordered endpoints, and no duplicate endpoint
pairs. -/
structure IndexedGraph (M E : ℕ) where
  left : Fin E → Fin M
  right : Fin E → Fin M
  ordered : ∀ e,left e<right e
  simple : Function.Injective (fun e => (left e,right e))

/-- The vertex `v` is one of the two endpoints of edge `e`. -/
def incident (G : IndexedGraph M E) (v : Fin M) (e : Fin E) : Prop :=
  G.left e=v ∨ G.right e=v

instance incidentDecidable (G : IndexedGraph M E) (v : Fin M) (e : Fin E) :
    Decidable (incident G v e) := by unfold incident;infer_instance

/-- Return the right endpoint when `v` is the left endpoint of `e`, and the left endpoint
otherwise. -/
def otherEndpoint (G : IndexedGraph M E) (v : Fin M) (e : Fin E) : Fin M :=
  if G.left e=v then G.right e else G.left e

/-- The edge `e` is incident to `v` and its other endpoint precedes `bound`. -/
def before (G : IndexedGraph M E) (v bound : Fin M) (e : Fin E) : Prop :=
  incident G v e ∧ otherEndpoint G v e<bound

instance beforeDecidable (G : IndexedGraph M E) (v bound : Fin M) (e : Fin E) :
    Decidable (before G v bound e) := by unfold before;infer_instance

/-- The finite set of edge indices incident to vertex `v`. -/
def incidentEdges (G : IndexedGraph M E) (v : Fin M) : Finset (Fin E) :=
  Finset.univ.filter (incident G v)

/-- The number of edges incident to vertex `v`. -/
def degree (G : IndexedGraph M E) (v : Fin M) : ℕ := (incidentEdges G v).card

/-- The Pauli word placing `Z` on the edges incident to vertex `v` and identity elsewhere. -/
def vertexWord (G : IndexedGraph M E) (v : Fin M) : PauliWord E :=
  fun e => if incident G v e then .Z else .I

/-- The graph edge Pauli word with `X` on edge `e` and `Z` on the selected preceding incident
edges at its endpoints. -/
def edgeWord (G : IndexedGraph M E) (e : Fin E) : PauliWord E :=
  fun f => if f=e then .X else
    if before G (G.left e) (G.right e) f ∨ before G (G.right e) (G.left e) f then .Z else .I

/-- The set of coordinates where a Pauli word differs from identity. -/
def support (w : PauliWord E) : Finset (Fin E) := Finset.univ.filter (fun e => w e≠.I)

/-- The support of a vertex Pauli word equals the set of incident edge indices. -/
theorem vertex_support (G : IndexedGraph M E) (v : Fin M) :
    support (vertexWord G v)=incidentEdges G v := by
  ext e
  simp only [support,incidentEdges,Finset.mem_filter,Finset.mem_univ,true_and,vertexWord]
  split_ifs <;> simp_all

/-- The support of an edge Pauli word is contained in the union of the incident edge sets of its
endpoints. -/
theorem edge_support_subset (G : IndexedGraph M E) (e : Fin E) :
    support (edgeWord G e)⊆incidentEdges G (G.left e)∪incidentEdges G (G.right e) := by
  intro f hf
  have hf' : edgeWord G e f≠.I := (Finset.mem_filter.1 hf).2
  by_cases he : f=e
  · subst f
    apply Finset.mem_union.2
    left
    simp [incidentEdges,incident]
  · have hp : before G (G.left e) (G.right e) f ∨ before G (G.right e) (G.left e) f := by
      by_contra h
      exact hf' (by simp [edgeWord,he,h])
    apply Finset.mem_union.2
    rcases hp with h|h
    · left
      simpa only [incidentEdges,Finset.mem_filter,Finset.mem_univ,true_and] using h.1
    · right
      simpa only [incidentEdges,Finset.mem_filter,Finset.mem_univ,true_and] using h.1

/-- The weight of a vertex Pauli word equals the degree of that vertex. -/
theorem vertex_weight (G : IndexedGraph M E) (v : Fin M) :
    (support (vertexWord G v)).card=degree G v := by rw [vertex_support];rfl

/-- The weight of an edge Pauli word is at most the sum of its endpoint degrees. -/
theorem edge_weight (G : IndexedGraph M E) (e : Fin E) :
    (support (edgeWord G e)).card≤degree G (G.left e)+degree G (G.right e) := by
  exact (Finset.card_le_card (edge_support_subset G e)).trans (Finset.card_union_le _ _)

/-- If all vertex degrees are at most `d`, vertex words have weight at most `d` and edge words
have weight at most `2 * d`. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem bounded_degree_support (G : IndexedGraph M E) (d : ℕ) (hd : ∀ v,degree G v≤d) :
    (∀ v,(support (vertexWord G v)).card≤d) ∧ ∀ e,(support (edgeWord G e)).card≤2*d := by
  refine ⟨fun v => by rw [vertex_weight];exact hd v,fun e => ?_⟩
  have he := edge_weight G e
  have hl := hd (G.left e)
  have hr := hd (G.right e)
  omega

/-- The matrix represented by the graph vertex Pauli word. -/
def vertexOperator (G : IndexedGraph M E) (v : Fin M) : Matrix (Reg E) (Reg E) ℂ :=
  pauliWordOp E (vertexWord G v)

/-- The matrix represented by the graph edge Pauli word. -/
def edgeOperator (G : IndexedGraph M E) (e : Fin E) : Matrix (Reg E) (Reg E) ℂ :=
  pauliWordOp E (edgeWord G e)

/-- All graph vertex and edge generator matrices are Hermitian and unitary. See [Setia and
Whitfield, 2018][SetiaWhitfield2018]. -/
theorem graph_generators (G : IndexedGraph M E) :
    (∀ v,(vertexOperator G v)ᴴ=vertexOperator G v ∧
      vertexOperator G v∈Matrix.unitaryGroup (Reg E) ℂ) ∧
    ∀ e,(edgeOperator G e)ᴴ=edgeOperator G e ∧ edgeOperator G e∈Matrix.unitaryGroup (Reg E) ℂ := by
  exact ⟨fun v => ⟨pauliWordOp_herm _ _,pauliWordOp_unitary _ _⟩,
    fun e => ⟨pauliWordOp_herm _ _,pauliWordOp_unitary _ _⟩⟩

end
end Qatlib.Papers.BKFermion17.GraphWords
