/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ScopedSearchInterface
import Qatlib.Concepts.WalkSearch.Primitives.TriangleContracts
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

def adjacent (S : Finset (Fin n×Fin n)) (a b : Fin n) : Prop := (a,b)∈S ∨ (b,a)∈S

theorem adjacent_symm (S : Finset (Fin n×Fin n)) (a b : Fin n) : adjacent S a b↔adjacent S b a := by
  exact or_comm

theorem mem_nbrOf_iff (S : Finset (Fin n×Fin n)) (a b : Fin n) : b∈nbrOf S a↔adjacent S a b := by
  simp only [nbrOf,Finset.mem_union,Finset.mem_image,Finset.mem_filter,adjacent]
  constructor
  · rintro (⟨⟨x,y⟩,⟨hxy,hx⟩,hy⟩ | ⟨⟨x,y⟩,⟨hxy,hy⟩,hx⟩)
    · change x=a at hx
      change y=b at hy
      exact Or.inl (by simpa only [hx,hy] using hxy)
    · change x=b at hx
      change y=a at hy
      exact Or.inr (by simpa only [hx,hy] using hxy)
  · rintro (hab | hba)
    · exact Or.inl ⟨(a,b),⟨hab,rfl⟩,rfl⟩
    · exact Or.inr ⟨(b,a),⟨hba,rfl⟩,rfl⟩

theorem tri3_iff (S : Finset (Fin n×Fin n)) (a b c : Fin n) :
    tri3 S a b c↔a≠b ∧ b≠c ∧ a≠c ∧ adjacent S a b ∧ adjacent S b c ∧ adjacent S a c := by
  simp only [tri3,tri3B,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne,adjacent]
  tauto

theorem mem_trianglesOf_iff (S : Finset (Fin n×Fin n)) (a b c : Fin n) :
    (a,b,c)∈trianglesOf S↔a<b ∧ b<c ∧ adjacent S a b ∧ adjacent S b c ∧ adjacent S a c := by
  simp only [trianglesOf,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← tri3,tri3_iff]
  constructor
  · rintro ⟨hab,hbc,_,_,_,h1,h2,h3⟩
    exact ⟨hab,hbc,h1,h2,h3⟩
  · rintro ⟨hab,hbc,h1,h2,h3⟩
    exact ⟨hab,hbc,hab.ne,hbc.ne,(hab.trans hbc).ne,h1,h2,h3⟩

theorem nbrOf_mono {S T : Finset (Fin n×Fin n)} (h : S⊆T) (a : Fin n) : nbrOf S a⊆nbrOf T a := by
  intro b hb
  rw [mem_nbrOf_iff] at hb ⊢
  exact hb.imp (fun hs=>h hs) (fun hs=>h hs)

theorem tOf_mono {S T : Finset (Fin n×Fin n)} (h : S⊆T) (a b : Fin n) : tOf S a b≤tOf T a b := by
  exact Finset.card_le_card (Finset.inter_subset_inter (nbrOf_mono h a) (nbrOf_mono h b))

theorem tOf_symm (S : Finset (Fin n×Fin n)) (a b : Fin n) : tOf S a b=tOf S b a := by
  simp only [tOf,Finset.inter_comm]
end Qatlib.Concepts.WalkSearch.Primitives
