/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationGraphSteps

/-!
# Incident pair and neighborhood crossing bounds

The module bounds the number of incident pairs and the graph edges selected by high degree
classification. `forwardGraphCross_card` uses the thin pair hypothesis to control one crossing
orientation, leading to the two orientation estimate `highEadd_graph_card`. For background on
quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `pairsAt_card_le_twice_degree`: The number of pairs incident to `v` in `S` is at most twice
  `degOf S v`.
* `highEadd_graph_card`: Under symmetry and the thin pair hypothesis, at most `2 * n * (tThin +
  1)` graph edges lie in `highEadd G S v`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators
variable {n : ℕ}

/-- The number of pairs incident to `v` in `S` is at most twice `degOf S v`. -/
theorem pairsAt_card_le_twice_degree (S : Finset (Fin n×Fin n)) (v : Fin n) :
    (pairsAt S v).card≤2*degOf S v := by
  have hs : pairsAt S v⊆(nbrOf S v).image (fun x=>(v,x))∪(nbrOf S v).image (fun x=>(x,v)) := by
    rintro ⟨a,b⟩ h
    have hh := Finset.mem_filter.mp h
    rcases hh.2 with he | he
    · change a=v at he
      subst a
      exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨b,(mem_nbrOf_iff S v b).mpr (Or.inl hh.1),rfl⟩)
    · change b=v at he
      subst b
      exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨a,(mem_nbrOf_iff S v a).mpr (Or.inr hh.1),rfl⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have h1 : ((nbrOf S v).image (fun x=>(v,x))).card≤(nbrOf S v).card := Finset.card_image_le
  have h2 : ((nbrOf S v).image (fun x=>(x,v))).card≤(nbrOf S v).card := Finset.card_image_le
  dsimp [degOf]
  omega

/-- Intersecting the pairs of `S` incident to `v` with the graph edges equals taking incident
pairs after intersecting `G.edges` with `S`. -/
theorem pairsAt_inter_graph (G : UGraph n) (S : Finset (Fin n×Fin n)) (v : Fin n) :
    pairsAt S v∩G.edges=pairsAt (G.edges∩S) v := by
  ext p
  simp only [pairsAt,Finset.mem_filter,Finset.mem_inter]
  tauto

/-- The graph edges in `S` whose first endpoint is a graph neighbor of `v` and whose second
endpoint is a neighbor of `v` in `S`. -/
def forwardGraphCross (G : UGraph n) (S : Finset (Fin n×Fin n)) (v : Fin n) : Finset (Fin n×Fin n) :=
  (S∩G.edges).filter fun p=>p.1∈nbrOf G.edges v ∧ p.2∈nbrOf S v

/-- If the symmetric candidate set is contained in `thinPairs G.edges tThin`, then
`forwardGraphCross G S v` has at most `n * tThin` elements. -/
theorem forwardGraphCross_card (G : UGraph n) (S : Finset (Fin n×Fin n))
    (hS : pairSetSymmetric S) (v : Fin n) (tThin : ℕ) (hthin : S⊆thinPairs G.edges tThin) :
    (forwardGraphCross G S v).card≤n*tThin := by
  let target := (nbrOf S v).biUnion (fun y=>(nbrOf G.edges v∩nbrOf G.edges y).image (fun x=>(x,y)))
  have hs : forwardGraphCross G S v⊆target := by
    rintro ⟨x,y⟩ h
    obtain ⟨he,hx,hy⟩:=Finset.mem_filter.mp h
    have heG := (Finset.mem_inter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨y,hy,Finset.mem_image.mpr ⟨x,Finset.mem_inter.mpr ⟨hx,(mem_graph_nbr_iff G y x).mpr (G.symm x y heG)⟩,rfl⟩⟩
  have hc : target.card≤(nbrOf S v).card*tThin := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _y∈nbrOf S v,tThin := Finset.sum_le_sum (fun y hy=>
        Finset.card_image_le.trans (by
          have hp := hthin ((mem_symmetric_nbr_iff S hS v y).mp hy)
          exact (Finset.mem_filter.mp hp).2))
      _ = _ := by simp
  exact (Finset.card_le_card hs).trans
      (hc.trans (Nat.mul_le_mul_right tThin ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))))

/-- Under symmetry and the thin pair hypothesis, at most `2 * n * (tThin + 1)` graph edges lie
in `highEadd G S v`. -/
theorem highEadd_graph_card (G : UGraph n) (S : Finset (Fin n×Fin n))
    (hS : pairSetSymmetric S) (v : Fin n) (tThin : ℕ) (hthin : S⊆thinPairs G.edges tThin) :
    (highEadd G S v∩G.edges).card≤2*n*(tThin+1) := by
  let C:=forwardGraphCross G S v
  let I:=pairsAt G.edges v
  have hs : highEadd G S v∩G.edges⊆I∪(C∪C.image Prod.swap) := by
    rintro ⟨a,b⟩ h
    obtain ⟨he,hG⟩:=Finset.mem_inter.mp h
    obtain ⟨hS1,ha | hb | hforward | hback⟩:=Finset.mem_filter.mp he
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hG,Or.inl ha⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hG,Or.inr hb⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hS1,hG⟩,hforward⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(b,a),Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hS a b hS1,G.symm a b hG⟩,hback⟩,rfl⟩))
  have h0 := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have h1 : I.card≤2*n :=
      (pairsAt_card_le_twice_degree G.edges v).trans
      (Nat.mul_le_mul_left 2 ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n)))
  have h2 : C.card≤n*tThin := forwardGraphCross_card G S hS v tThin hthin
  have h3 : (C.image Prod.swap).card≤C.card := Finset.card_image_le
  have h4 : (C∪C.image Prod.swap).card≤C.card+(C.image Prod.swap).card := Finset.card_union_le _ _
  nlinarith
end Qatlib.Concepts.WalkSearch.MainResults
