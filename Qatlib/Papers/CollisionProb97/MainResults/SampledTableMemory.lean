/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.DistinctImageTable
import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.SampledTableMemory
open DistinctImageTable
variable {S R : Type} [DecidableEq R]

def memory {F : S → R} {n : ℕ} (s : Records F n) :
    ReadOnlyTable.Memory (X := S) (R := R) n :=
  fun i => s.entries.get ⟨i.val, by rw [s.length_eq]; exact i.isLt⟩

omit [DecidableEq R] in

theorem memory_mem {F : S → R} {n : ℕ} (s : Records F n) (i : Fin n) :
    memory s i ∈ s.entries := by
  exact List.get_mem _ _

omit [DecidableEq R] in

theorem mem_memory {F : S → R} {n : ℕ} (s : Records F n) (p : S × R)
    (hp : p ∈ s.entries) : ∃ i, memory s i = p := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  refine ⟨⟨i.val, by simpa only [s.length_eq] using i.isLt⟩, ?_⟩
  exact hi

theorem memory_values {F : S → R} {n : ℕ} (s : Records F n) :
    ReadOnlyTable.values (memory s) = values s := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨memory s i, memory_mem s i, hi⟩)
  · intro hz
    obtain ⟨p, hp, hz⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    obtain ⟨i, hi⟩ := mem_memory s p hp
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simpa only [hi] using hz⟩

omit [DecidableEq R] in

theorem memory_accurate {F : S → R} {n : ℕ} (s : Records F n) (i : Fin n) :
    (memory s i).2 = F (memory s i).1 := s.accurate _ (memory_mem s i)

theorem memory_card {F : S → R} {n : ℕ} (s : Records F n) :
    (ReadOnlyTable.values (memory s)).card = n := by
  rw [memory_values, values_card]

end Qatlib.Papers.CollisionProb97.MainResults.SampledTableMemory
