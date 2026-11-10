/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.ConnectedWords
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
variable {N R M k d : ℕ} {J : ℝ}

theorem flatMap_sum {α β G : Type*} [AddMonoid G] (l : List α) (f : α→List β) (g : β→G) :
    ((l.flatMap f).map g).sum=(l.map (fun a=>((f a).map g).sum)).sum := by
  induction l with
  | nil=>simp
  | cons a l ih=>simpa only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons] using congrArg (fun x=>((f a).map g).sum+x) ih

theorem norm_map_sum_le {α G : Type*} [SeminormedAddCommGroup G] (l : List α) (f : α→G) :
    ‖(l.map f).sum‖ ≤ (l.map (fun a=>‖f a‖)).sum := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    simp only [List.map_cons,List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

theorem commutator_list_sum {α : Type*} (l : List α) (f : α→Matrix (Register N) (Register N) ℂ)
    (A : Matrix (Register N) (Register N) ℂ) :
    A*(l.map f).sum-(l.map f).sum*A=(l.map (fun b=>A*f b-f b*A)).sum := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    simp only [List.map_cons,List.sum_cons]
    calc
      _=(A*f a-f a*A)+(A*(l.map f).sum-(l.map f).sum*A) := by noncomm_ring
      _=_ := by rw [ih]

def groupNested (h : Hamiltonian N R M k d J) (seed : Fin R) : List (Fin M)→Matrix (Register N) (Register N) ℂ
  | []=>h.term seed
  | m::xs=>h.grouped m*h.groupNested seed xs-h.groupNested seed xs*h.grouped m

theorem connected_expansion (h : Hamiltonian N R M k d J) (seed : Fin R) (xs : List (Fin M)) :
    h.groupNested seed xs=((h.words seed xs).map (h.nested seed)).sum := by
  induction xs with
  | nil=>simp [groupNested,words,nested]
  | cons m xs ih=>
    rw [groupNested,ih,commutator_list_sum]
    rw [words,flatMap_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro w hw
    rw [h.grouped_commutator m (h.region seed w) (h.nested seed w) (h.nested_supported seed w)]
    simp only [List.map_map,nested,Function.comp_def]
    simpa only [Finset.toList_toFinset] using (List.sum_toFinset (fun i=>h.term i*h.nested seed w-h.nested seed w*h.term i)
      (Finset.nodup_toList (h.active m (h.region seed w))))

theorem groupNested_norm (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (seed : Fin R) (xs : List (Fin M)) :
    ‖h.groupNested seed xs‖ ≤ ((k*d)^xs.length*xs.length.factorial:ℕ)*J^(xs.length+1) := by
  rw [h.connected_expansion]
  calc
    _ ≤ ((h.words seed xs).map (fun w=>‖h.nested seed w‖)).sum := norm_map_sum_le _ _
    _ ≤ ((h.words seed xs).map (fun _=>J^(xs.length+1))).sum := List.sum_le_sum (fun w hw=>by
      simpa only [h.words_length seed xs w hw] using h.nested_norm hJ seed w)
    _ = (h.words seed xs).length*J^(xs.length+1) := by
      induction h.words seed xs with
      | nil=>simp
      | cons w l ih=>simp only [List.map_cons,List.sum_cons,List.length_cons] at *; push_cast; rw [ih]; ring
    _ ≤ ((k*d)^xs.length*xs.length.factorial:ℕ)*J^(xs.length+1) := by
      gcongr
      exact h.words_count seed xs

end Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
