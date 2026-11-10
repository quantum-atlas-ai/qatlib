/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationSpecification
import Qatlib.Concepts.WalkSearch.MainResults.PromisedEdgeSearch
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical
variable {n : ℕ}

def triangleMarked (G : UGraph n) (T : Finset (Fin n×Fin n)) : {t //t∈trianglesOf T}→Bool :=
  fun t=>decide ((t.val.1,t.val.2.1)∈G.edges ∧ (t.val.1,t.val.2.2)∈G.edges ∧ (t.val.2.1,t.val.2.2)∈G.edges)

theorem triangleMarked_sound (G : UGraph n) (T : Finset (Fin n×Fin n)) (t : {t //t∈trianglesOf T})
    (hm : triangleMarked G T t=true) :
    tri3 G.edges t.val.1 t.val.2.1 t.val.2.2 ∧ (t.val.1,t.val.2.1)∈G.edges ∧
      (t.val.1,t.val.2.2)∈G.edges ∧ (t.val.2.1,t.val.2.2)∈G.edges := by
  have ht:=(mem_trianglesOf_iff T _ _ _).mp t.property
  have hg : (t.val.1,t.val.2.1)∈G.edges ∧ (t.val.1,t.val.2.2)∈G.edges ∧ (t.val.2.1,t.val.2.2)∈G.edges := by
    simpa only [triangleMarked,decide_eq_true_eq] using hm
  exact ⟨(tri3_iff _ _ _ _).mpr ⟨ht.1.ne,ht.2.1.ne,(ht.1.trans ht.2.1).ne,
    Or.inl hg.1,Or.inl hg.2.2,Or.inl hg.2.1⟩,hg⟩

def edgeTriangleExists (G : UGraph n) (E : Finset (Fin n×Fin n)) : Prop :=
  ∃ a b c : Fin n,a≠b ∧ b≠c ∧ a≠c ∧ (a,b)∈E ∧ (a,b)∈G.edges ∧ (a,c)∈G.edges ∧ (b,c)∈G.edges

theorem true_triangle_partition_coverage (G : UGraph n) (T E : Finset (Fin n×Fin n))
    (hG : G.edges⊆T∪E) (htri : 1≤triCount G.edges) :
    (∃ t : {t //t∈trianglesOf T},triangleMarked G T t=true) ∨ edgeTriangleExists G E := by
  obtain ⟨⟨a,b,c⟩,ht⟩:=Finset.one_le_card.mp htri
  obtain ⟨hab,hbc,hAB,hBC,hAC⟩:=(mem_trianglesOf_iff G.edges a b c).mp ht
  have h1 : (a,b)∈G.edges := hAB.elim id (G.symm b a)
  have h2 : (b,c)∈G.edges := hBC.elim id (G.symm c b)
  have h3 : (a,c)∈G.edges := hAC.elim id (G.symm c a)
  by_cases hE1 : (a,b)∈E
  · exact Or.inr ⟨a,b,c,hab.ne,hbc.ne,(hab.trans hbc).ne,hE1,h1,h3,h2⟩
  by_cases hE2 : (b,c)∈E
  · exact Or.inr ⟨b,c,a,hbc.ne,(hab.trans hbc).ne.symm,hab.ne.symm,hE2,h2,G.symm a b h1,G.symm a c h3⟩
  by_cases hE3 : (a,c)∈E
  · exact Or.inr ⟨a,c,b,(hab.trans hbc).ne,hbc.ne.symm,hab.ne,hE3,h3,h1,G.symm b c h2⟩
  have hT1 : (a,b)∈T := (Finset.mem_union.mp (hG h1)).resolve_right hE1
  have hT2 : (b,c)∈T := (Finset.mem_union.mp (hG h2)).resolve_right hE2
  have hT3 : (a,c)∈T := (Finset.mem_union.mp (hG h3)).resolve_right hE3
  have hmem : (a,b,c)∈trianglesOf T :=
      (mem_trianglesOf_iff T a b c).mpr ⟨hab,hbc,Or.inl hT1,Or.inl hT2,Or.inl hT3⟩
  refine Or.inl ⟨⟨(a,b,c),hmem⟩,?_⟩
  exact decide_eq_true ⟨h1,h3,h2⟩
end Qatlib.Concepts.WalkSearch.MainResults
