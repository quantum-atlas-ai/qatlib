/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationGraphSteps

/-!
# Symmetric draining of candidate pairs

`drainPaired` repeatedly removes a pair with common neighbor count below `τ`, together with its
reverse when present, and records the removed pairs. The module proves a disjoint partition into
removed and remaining pairs, preservation of symmetry, and the threshold condition once the fuel
covers the initial pair count. For background on quantum search and amplitude amplification, see
[BrassardEtAl2002].

## Main statements

* `edgePairBlock`: The elements of `S` equal to `p` or its coordinate swap.
* `drainPaired_fixpoint`: If the fuel is at least `S.card`, each remaining pair has common
  neighbor count at least `τ` within the remaining set.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators
variable {n : ℕ}

/-- The elements of `S` equal to `p` or its coordinate swap. -/
def edgePairBlock (S : Finset (Fin n×Fin n)) (p : Fin n×Fin n) : Finset (Fin n×Fin n) :=
  S.filter fun e=>e=p ∨ e=p.swap

/-- Use the given fuel to remove pairs with common neighbor count below `τ` together with their
reverses, returning the remaining set and the list of removed pairs. -/
def drainPaired (S : Finset (Fin n×Fin n)) (τ : ℕ) : ℕ→Finset (Fin n×Fin n)×List (Fin n×Fin n)
  | 0=>(S,[])
  | fuel+1=>
    match (S.filter (fun p=>tOf S p.1 p.2<τ)).toList.head? with
    | none=>(S,[])
    | some p=>
      let D:=edgePairBlock S p
      let result:=drainPaired (S\D) τ fuel
      (result.1,D.toList++result.2)

/-- Every pair in `edgePairBlock S p` belongs to `S`. -/
theorem edgePairBlock_subset (S : Finset (Fin n×Fin n)) (p : Fin n×Fin n) : edgePairBlock S p⊆S :=
    Finset.filter_subset _ _

/-- The block containing `p` and its reverse is symmetric when `S` is symmetric. -/
theorem edgePairBlock_symmetric (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) (p : Fin n×Fin n) :
    pairSetSymmetric (edgePairBlock S p) := by
  intro a b h
  simp only [edgePairBlock,Finset.mem_filter] at h ⊢
  refine ⟨hS a b h.1,?_⟩
  rcases h.2 with he | he
  · exact Or.inr (congrArg Prod.swap he)
  · exact Or.inl (by simpa only [Prod.swap_swap] using! congrArg Prod.swap he)

/-- The remaining set and the finite set of removed pairs are disjoint subsets of `S` whose
union equals `S`. -/
theorem drainPaired_partition (S : Finset (Fin n×Fin n)) (τ fuel : ℕ) :
    (drainPaired S τ fuel).1⊆S ∧ (drainPaired S τ fuel).2.toFinset⊆S ∧
    (drainPaired S τ fuel).1∪(drainPaired S τ fuel).2.toFinset=S ∧
    Disjoint (drainPaired S τ fuel).1 (drainPaired S τ fuel).2.toFinset := by
  induction fuel generalizing S with
  | zero => simp [drainPaired]
  | succ fuel ih =>
    rw [drainPaired]
    cases hh : (S.filter (fun p=>tOf S p.1 p.2<τ)).toList.head? with
    | none => simp
    | some p =>
      (try dsimp only)
      let D:=edgePairBlock S p
      obtain ⟨hleft,htrace,hunion,hdis⟩:=ih (S\D)
      simp only [List.toFinset_append,Finset.toList_toFinset]
      refine ⟨hleft.trans Finset.sdiff_subset,Finset.union_subset (edgePairBlock_subset S p) (htrace.trans Finset.sdiff_subset),?_,?_⟩
      · ext e
        have hdS : D⊆S := edgePairBlock_subset S p
        have hU : e∈(drainPaired (S\D) τ fuel).1 ∪ (drainPaired (S\D) τ fuel).2.toFinset↔e∈S ∧
            e∉D := by rw [hunion];exact Finset.mem_sdiff
        simp only [Finset.mem_union] at hU ⊢
        dsimp only [D] at hU
        constructor
        · rintro (hl | hd | ht)
          · exact (hU.mp (Or.inl hl)).1
          · exact hdS hd
          · exact (hU.mp (Or.inr ht)).1
        · intro he
          by_cases hd : e∈D
          · exact Or.inr (Or.inl hd)
          · exact (hU.mpr ⟨he,hd⟩).elim Or.inl (fun ht=>Or.inr (Or.inr ht))
      · apply Finset.disjoint_left.mpr
        intro e he hf
        rcases Finset.mem_union.mp hf with hd | ht
        · exact (Finset.mem_sdiff.mp (hleft he)).2 hd
        · exact Finset.disjoint_left.mp hdis he ht

/-- Paired draining preserves symmetry of the remaining pair set for every fuel value. -/
theorem drainPaired_symmetric (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) (τ fuel : ℕ) :
    pairSetSymmetric (drainPaired S τ fuel).1 := by
  induction fuel generalizing S with
  | zero => exact hS
  | succ fuel ih =>
    rw [drainPaired]
    cases hh : (S.filter (fun p=>tOf S p.1 p.2<τ)).toList.head? with
    | none => exact hS
    | some p => exact ih _ (symmetric_sdiff hS (edgePairBlock_symmetric S hS p))

/-- If the fuel is at least `S.card`, each remaining pair has common neighbor count at least `τ`
within the remaining set. -/
theorem drainPaired_fixpoint (S : Finset (Fin n×Fin n)) (τ fuel : ℕ) (hFuel : S.card≤fuel) :
    ∀ a b,(a,b)∈(drainPaired S τ fuel).1→τ≤tOf (drainPaired S τ fuel).1 a b := by
  induction fuel generalizing S with
  | zero =>
    have he : S=∅ := Finset.card_eq_zero.mp (by omega)
    simp [drainPaired,he]
  | succ fuel ih =>
    rw [drainPaired]
    cases hh : (S.filter (fun p=>tOf S p.1 p.2<τ)).toList.head? with
    | none =>
      have he : S.filter (fun p=>tOf S p.1 p.2<τ)=∅ := by
        have ht := List.head?_eq_none_iff.mp hh
        exact Finset.toList_eq_nil.mp ht
      change ∀ a b,(a,b)∈S→τ≤tOf S a b
      intro a b hab
      by_contra h
      have hm : (a,b)∈S.filter (fun p=>tOf S p.1 p.2<τ) :=
          Finset.mem_filter.mpr ⟨hab,by (try dsimp only);omega⟩
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    | some p =>
      have hp : p∈S ∧ tOf S p.1 p.2<τ := by
        have hm := List.mem_of_head? hh
        exact Finset.mem_filter.mp (Finset.mem_toList.mp hm)
      have hd : 0<(edgePairBlock S p).card :=
          Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨hp.1,Or.inl rfl⟩⟩
      have hc := Finset.card_sdiff_add_card_eq_card (edgePairBlock_subset S p)
      exact ih _ (by omega)
end Qatlib.Concepts.WalkSearch.MainResults
