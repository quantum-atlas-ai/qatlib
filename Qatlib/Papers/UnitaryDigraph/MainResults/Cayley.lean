/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian.Theorem3
import Qatlib.Papers.UnitaryDigraph.MainResults.Defs

/-!
# Unitary line digraphs of finite Cayley digraphs

This module identifies the incoming and outgoing neighborhoods of a Cayley digraph and proves
that each has cardinality equal to the size of the generator set. The resulting degree balance
gives the Eulerian predicate, and for a finite group the line digraph is the support digraph of
a unitary matrix. See [Severini2003].

## Main statements

* `cayley_eulerian`: Incoming and outgoing neighborhood cardinalities agree.
* `corollary3`: The line digraph of a finite Cayley digraph is a unitary digraph.

## References

* [Severini, 2003][Severini2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Cayley

open Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs

/-- The outgoing neighborhood of `g` in a Cayley digraph is the image of the generator set under
left multiplication by `g`. -/
theorem cayley_outNbrs (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    (CayleyDigraph G S).outNbrs g = (S.image (fun s => g * s) : Set G) := by
  ext h
  rw [Defs.Digraph.mem_outNbrs]
  simp only [CayleyDigraph, Finset.mem_coe, Finset.mem_image]

/-- The incoming neighborhood of `g` is the image of the generator set under `s ↦ g * s⁻¹`. -/
theorem cayley_inNbrs (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    (CayleyDigraph G S).inNbrs g = (S.image (fun s => g * s⁻¹) : Set G) := by
  ext h
  rw [Defs.Digraph.mem_inNbrs]
  simp only [CayleyDigraph, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hsg⟩
    exact ⟨s, hs, by rw [← hsg]; group⟩
  · rintro ⟨s, hs, hsg⟩
    exact ⟨s, hs, by rw [← hsg]; group⟩

/-- The outgoing neighborhood of each group element has cardinality `S.card`. -/
theorem ncard_cayley_out (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    ((CayleyDigraph G S).outNbrs g).ncard = S.card := by
  rw [cayley_outNbrs, Set.ncard_coe_finset,
    Finset.card_image_of_injective S (mul_right_injective g)]

/-- The incoming neighborhood of each group element has cardinality `S.card`. -/
theorem ncard_cayley_in (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    ((CayleyDigraph G S).inNbrs g).ncard = S.card := by
  have hinj : Function.Injective (fun s => g * s⁻¹) :=
    fun a b h => inv_injective (mul_right_injective g h)
  rw [cayley_inNbrs, Set.ncard_coe_finset, Finset.card_image_of_injective S hinj]

/-- Every Cayley digraph defined by a finite generator set satisfies the Eulerian degree-balance
predicate. See [Severini2003]. -/
theorem cayley_eulerian (G : Type) [Group G] [DecidableEq G] (S : Finset G) :
    Eulerian (CayleyDigraph G S) := by
  intro g
  rw [ncard_cayley_in G S g, ncard_cayley_out G S g]

/-- The line digraph of a Cayley digraph on a finite group is the support digraph of a complex
unitary matrix. See [Severini, Corollary 3][Severini2003]. -/
theorem corollary3 (G : Type) [Group G] [Fintype G] [DecidableEq G] (S : Finset G)
    [Fintype (Arc (CayleyDigraph G S))] [DecidableEq (Arc (CayleyDigraph G S))] :
    IsUnitaryDigraph (lineDigraph (CayleyDigraph G S)) :=
  isUnitaryDigraph_lineDigraph_of_eulerian (CayleyDigraph G S) (cayley_eulerian G S)

end Qatlib.Papers.UnitaryDigraph.MainResults.Cayley
