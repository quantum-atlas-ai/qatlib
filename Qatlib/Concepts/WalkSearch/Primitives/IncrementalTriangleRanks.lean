/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.GraphVocabulary
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

def edgeAdmissionRank (l : List (Fin n×Fin n)) (e : Fin n×Fin n) : ℕ :=
  l.findIdx (fun p=>decide (p=e ∨ p=e.swap))

theorem edgeAdmissionRank_swap (l : List (Fin n×Fin n)) (e : Fin n×Fin n) :
    edgeAdmissionRank l e.swap=edgeAdmissionRank l e := by
  unfold edgeAdmissionRank
  congr 1
  funext p
  simp only [Prod.swap_swap,or_comm]

theorem edgeAdmissionRank_lt_of_adjacent (l : List (Fin n×Fin n)) (a b : Fin n)
    (h : adjacent l.toFinset a b) : edgeAdmissionRank l (a,b) < l.length := by
  apply List.findIdx_lt_length_of_exists
  rcases h with hab | hba
  · exact ⟨(a,b),by simpa only [List.mem_toFinset] using hab,by simp⟩
  · exact ⟨(b,a),by simpa only [List.mem_toFinset] using hba,by simp⟩

theorem edgeAdmissionRank_getElem (l : List (Fin n×Fin n)) (e : Fin n×Fin n)
    (h : edgeAdmissionRank l e < l.length) :
    l[edgeAdmissionRank l e]=e ∨ l[edgeAdmissionRank l e]=e.swap := by
  have hh := List.findIdx_getElem (xs := l) (p := fun p=>decide (p=e ∨ p=e.swap)) (w := h)
  simpa only [decide_eq_true_eq] using! hh

theorem adjacent_prefix_of_rank_lt (l : List (Fin n×Fin n)) (a b : Fin n) (i : ℕ)
    (hr : edgeAdmissionRank l (a,b) < i) (hi : i ≤ l.length) : adjacent (l.take i).toFinset a b := by
  have hl : edgeAdmissionRank l (a,b) < l.length := hr.trans_le hi
  have hm : l[edgeAdmissionRank l (a,b)]∈l.take i := by
    apply List.mem_take_iff_getElem.mpr
    exact ⟨edgeAdmissionRank l (a,b),Nat.lt_min.mpr ⟨hr,hl⟩,rfl⟩
  rcases edgeAdmissionRank_getElem l (a,b) hl with he | he
  · exact Or.inl (by rw [List.mem_toFinset];simpa only [he] using hm)
  · exact Or.inr (by rw [List.mem_toFinset];simpa only [he] using! hm)

theorem canonical_rank_injective (l : List (Fin n×Fin n)) (e f : Fin n×Fin n)
    (he : e.1 < e.2) (hf : f.1 < f.2) (heR : edgeAdmissionRank l e < l.length)
    (hfR : edgeAdmissionRank l f < l.length) (hR : edgeAdmissionRank l e=edgeAdmissionRank l f) : e=f := by
  have heL := edgeAdmissionRank_getElem l e heR
  have hfL := edgeAdmissionRank_getElem l f hfR
  simp only [← hR] at hfL
  rcases heL with heL | heL  <;> rcases hfL with hfL | hfL
  · exact heL.symm.trans hfL
  · have hh := heL.symm.trans hfL
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp only [Prod.fst_swap,Prod.snd_swap] at h1 h2
    omega
  · have hh := heL.symm.trans hfL
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp only [Prod.fst_swap,Prod.snd_swap] at h1 h2
    omega
  · exact congrArg Prod.swap (heL.symm.trans hfL)
end Qatlib.Concepts.WalkSearch.Primitives
