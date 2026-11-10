/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian.Theorem3
import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Cayley

open Qatlib.Papers.UnitaryDigraph.MainResults.Eulerian
open Qatlib.Papers.UnitaryDigraph.MainResults.Defs

theorem cayley_outNbrs (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    (CayleyDigraph G S).outNbrs g = (S.image (fun s => g * s) : Set G) := by
  ext h
  rw [Defs.Digraph.mem_outNbrs]
  simp only [CayleyDigraph, Finset.mem_coe, Finset.mem_image]

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

theorem ncard_cayley_out (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    ((CayleyDigraph G S).outNbrs g).ncard = S.card := by
  rw [cayley_outNbrs, Set.ncard_coe_finset,
    Finset.card_image_of_injective S (mul_right_injective g)]

theorem ncard_cayley_in (G : Type) [Group G] [DecidableEq G] (S : Finset G) (g : G) :
    ((CayleyDigraph G S).inNbrs g).ncard = S.card := by
  have hinj : Function.Injective (fun s => g * s⁻¹) :=
    fun a b h => inv_injective (mul_right_injective g h)
  rw [cayley_inNbrs, Set.ncard_coe_finset, Finset.card_image_of_injective S hinj]

theorem cayley_eulerian (G : Type) [Group G] [DecidableEq G] (S : Finset G) :
    Eulerian (CayleyDigraph G S) := by
  intro g
  rw [ncard_cayley_in G S g, ncard_cayley_out G S g]

theorem corollary3 (G : Type) [Group G] [Fintype G] [DecidableEq G] (S : Finset G)
    [Fintype (Arc (CayleyDigraph G S))] [DecidableEq (Arc (CayleyDigraph G S))] :
    IsUnitaryDigraph (lineDigraph (CayleyDigraph G S)) :=
  isUnitaryDigraph_lineDigraph_of_eulerian (CayleyDigraph G S) (cayley_eulerian G S)

end Qatlib.Papers.UnitaryDigraph.MainResults.Cayley
