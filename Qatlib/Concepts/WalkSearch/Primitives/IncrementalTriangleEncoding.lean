/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.IncrementalTriangleRanks
import Qatlib.Concepts.WalkSearch.Primitives.CanonicalEdgeCounting
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

def triangleLastEdge (l : List (Fin n×Fin n)) (x : Fin n×Fin n×Fin n) : (Fin n×Fin n)×Fin n :=
  let a:=x.1;let b:=x.2.1;let c:=x.2.2
  if edgeAdmissionRank l (a,b) ≤ edgeAdmissionRank l (b,c) ∧ edgeAdmissionRank l (a,c) ≤ edgeAdmissionRank l (b,c)
    then ((b,c),a)
  else if edgeAdmissionRank l (a,b) ≤ edgeAdmissionRank l (a,c) then ((a,c),b) else ((a,b),c)

theorem triangleLastEdge_good (l : List (Fin n×Fin n)) (x : Fin n×Fin n×Fin n)
    (hx : x∈trianglesOf l.toFinset) :
    (triangleLastEdge l x).1.1 < (triangleLastEdge l x).1.2 ∧
    edgeAdmissionRank l (triangleLastEdge l x).1 < l.length ∧
    (triangleLastEdge l x).2∈nbrOf (l.take (edgeAdmissionRank l (triangleLastEdge l x).1)).toFinset (triangleLastEdge l x).1.1 ∩
      nbrOf (l.take (edgeAdmissionRank l (triangleLastEdge l x).1)).toFinset (triangleLastEdge l x).1.2 := by
  rcases x with ⟨a,b,c⟩
  obtain ⟨hab,hbc,hAB,hBC,hAC⟩ := (mem_trianglesOf_iff _ _ _ _).mp hx
  have hACord : a < c := hab.trans hbc
  have rAB := edgeAdmissionRank_lt_of_adjacent l a b hAB
  have rBC := edgeAdmissionRank_lt_of_adjacent l b c hBC
  have rAC := edgeAdmissionRank_lt_of_adjacent l a c hAC
  have neABBC : edgeAdmissionRank l (a,b)≠edgeAdmissionRank l (b,c) := by
    intro h
    have hh := canonical_rank_injective l (a,b) (b,c) hab hbc rAB rBC h
    exact hab.ne (congrArg Prod.fst hh)
  have neABAC : edgeAdmissionRank l (a,b)≠edgeAdmissionRank l (a,c) := by
    intro h
    have hh := canonical_rank_injective l (a,b) (a,c) hab hACord rAB rAC h
    exact hbc.ne (congrArg Prod.snd hh)
  have neBCAC : edgeAdmissionRank l (b,c)≠edgeAdmissionRank l (a,c) := by
    intro h
    have hh := canonical_rank_injective l (b,c) (a,c) hbc hACord rBC rAC h
    exact hab.ne (congrArg Prod.fst hh).symm
  unfold triangleLastEdge
  (try dsimp only)
  split_ifs with hmax hmid
  all_goals (try dsimp only)
  · refine ⟨hbc,rBC,?_⟩
    rw [Finset.mem_inter,mem_nbrOf_iff,mem_nbrOf_iff]
    constructor
    · exact (adjacent_symm _ _ _).mp (adjacent_prefix_of_rank_lt l a b _ (by omega) rBC.le)
    · exact (adjacent_symm _ _ _).mp (adjacent_prefix_of_rank_lt l a c _ (by omega) rBC.le)
  · refine ⟨hACord,rAC,?_⟩
    rw [Finset.mem_inter,mem_nbrOf_iff,mem_nbrOf_iff]
    constructor
    · exact adjacent_prefix_of_rank_lt l a b _ (by omega) rAC.le
    · exact (adjacent_symm _ _ _).mp (adjacent_prefix_of_rank_lt l b c _ (by omega) rAC.le)
  · refine ⟨hab,rAB,?_⟩
    rw [Finset.mem_inter,mem_nbrOf_iff,mem_nbrOf_iff]
    constructor
    · exact adjacent_prefix_of_rank_lt l a c _ (by omega) rAB.le
    · exact adjacent_prefix_of_rank_lt l b c _ (by omega) rAB.le

theorem triangleLastEdge_injective (l : List (Fin n×Fin n)) : Set.InjOn (triangleLastEdge l) (trianglesOf l.toFinset) := by
  intro ⟨a,b,c⟩ hx ⟨a',b',c'⟩ hy he
  have hab := ((mem_trianglesOf_iff _ _ _ _).mp hx).1
  have hbc := ((mem_trianglesOf_iff _ _ _ _).mp hx).2.1
  have hab' := ((mem_trianglesOf_iff _ _ _ _).mp hy).1
  have hbc' := ((mem_trianglesOf_iff _ _ _ _).mp hy).2.1
  unfold triangleLastEdge at he
  dsimp only at he
  split_ifs at he  <;>
    (have hh := Prod.mk.inj he
     have h1 := congrArg Prod.fst hh.1
     have h2 := congrArg Prod.snd hh.1
     have h3 := hh.2
     dsimp only at h1 h2 h3
     ext <;> (try dsimp only) <;> omega)
end Qatlib.Concepts.WalkSearch.Primitives
