/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Actual path vertex covers by parity and disjoint edges

Demand: Childs--Kothari, arXiv1011.1443v2 Proposition4.1. The path
constructor is the exact historical consecutive-vertex relation. Its
bridge to the pinned paper constructor is verified separately.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.MinorClosed10.MainResults.PathCover

/-- The genuine k-edge path on consecutive vertices zero through k. -/
def pathG (k : ℕ) : SimpleGraph (Fin (k+1)) :=
  SimpleGraph.fromRel (fun i j : Fin (k+1) => i.val+1=j.val)

/-- The odd-indexed vertices of the actual consecutive path. -/
def odds (k : ℕ) : Set (Fin (k+1)) := {i | i.val%2=1}

/-- Consecutive vertices have opposite parity, so the odd vertices cover every actual path edge. -/
theorem oddsCover (k : ℕ) : (pathG k).IsVertexCover (odds k) := by
  intro a b hab
  change a ≠ b ∧ (a.val+1=b.val ∨ b.val+1=a.val) at hab
  change a.val%2=1 ∨ b.val%2=1
  rcases hab.2 with h | h <;> omega

/-- The actual odd vertices are in bijection with the first floor((k+1)/2) indices. -/
def oddEquiv (k : ℕ) : Fin ((k+1)/2) ≃ {v : Fin (k+1) // v ∈ odds k} where
  toFun i := ⟨⟨2*i.val+1, by have := i.isLt; omega⟩, by change (2*i.val+1)%2=1; omega⟩
  invFun v := ⟨v.1.val/2, by have := v.1.isLt; have := v.2; change v.1.val%2=1 at this; omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have hv := v.2
    change v.1.val%2=1 at hv
    dsimp
    omega

/-- The entire actual odd cover has exactly floor((k+1)/2) vertices. -/
theorem oddCard (k : ℕ) : (odds k).encard = (((k+1)/2 : ℕ) : ℕ∞) := by
  have he : Fintype.card {v : Fin (k+1) // v ∈ odds k} = (k+1)/2 := by
    rw [← Fintype.card_congr (oddEquiv k), Fintype.card_fin]
  simpa [Set.encard, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card] using
    congrArg (fun n : ℕ => (n : ℕ∞)) he

/-- Disjoint actual edges force every vertex cover to contain at least one distinct vertex per edge. -/
theorem matchLower {I V : Type} [Fintype I] [Fintype V] (G : SimpleGraph V)
    (e : I × Bool ↪ V) (he : ∀ i, G.Adj (e (i,false)) (e (i,true))) :
    (Fintype.card I : ℕ∞) ≤ G.vertexCoverNum := by
  unfold SimpleGraph.vertexCoverNum
  refine le_iInf fun c => le_iInf fun hc => ?_
  let pick : I → c := fun i =>
    if h : e (i,false) ∈ c then ⟨e (i,false), h⟩
    else ⟨e (i,true), (hc (he i)).resolve_left h⟩
  have hi : Function.Injective pick := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    dsimp only [pick] at hv
    split_ifs at hv <;> exact congrArg Prod.fst (e.injective hv)
  have hcard : Fintype.card I ≤ Fintype.card c := Fintype.card_le_of_injective pick hi
  simpa [Set.encard, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card] using
    (show (Fintype.card I : ℕ∞) ≤ (Fintype.card c : ℕ∞) by exact_mod_cast hcard)

/-- The actual even-odd consecutive pairs give an injective family of disjoint path edges. -/
def pairs (k : ℕ) : Fin ((k+1)/2) × Bool ↪ Fin (k+1) where
  toFun p := ⟨2*p.1.val+(if p.2 then 1 else 0), by have := p.1.isLt; split_ifs <;> omega⟩
  inj' := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    have hv := congrArg Fin.val h
    cases b <;> cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv
    all_goals first
      | (exfalso; omega)
      | (have hij : i = j := Fin.ext (by omega); subst j; rfl)

/-- Each genuine consecutive pair in the disjoint family is an actual edge of the path. -/
theorem pairAdj (k : ℕ) (i : Fin ((k+1)/2)) :
    (pathG k).Adj (pairs k (i,false)) (pairs k (i,true)) := by
  change pairs k (i,false) ≠ pairs k (i,true) ∧
    ((pairs k (i,false)).val+1=(pairs k (i,true)).val ∨
     (pairs k (i,true)).val+1=(pairs k (i,false)).val)
  constructor
  · exact (pairs k).injective.ne (by simp)
  · apply Or.inl
    change 2*i.val+0+1=2*i.val+1
    omega

/-- The whole genuine k-edge path has vertex-cover number floor((k+1)/2), including k zero. -/
theorem pathNumber (k : ℕ) : (pathG k).vertexCoverNum = (((k+1)/2 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact (oddsCover k).vertexCoverNum_le.trans_eq (oddCard k)
  · simpa using matchLower (pathG k) (pairs k) (pairAdj k)

end Qatlib.Papers.MinorClosed10.MainResults.PathCover
