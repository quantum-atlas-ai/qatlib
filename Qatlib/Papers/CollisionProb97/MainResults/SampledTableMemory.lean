/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.DistinctImageTable
import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable

/-!
# Converting sampled records to table memory

This module converts a collection of accurate distinct-image records into the indexed
`ReadOnlyTable.Memory` representation. It connects the sampled table stage to coherent lookup in
the claw algorithm of [BrassardHoyerTapp1998Collision].

The conversion `memory` preserves exactly the records, their value set, and their accuracy;
`memory_card` gives the resulting value cardinality.

## Main statements

* `memory_values`: Converting records to memory preserves their finite set of stored values.
* `memory_accurate`: Every converted memory record stores the correct `F`-value of its input
  [BrassardHoyerTapp1998Collision].
* `memory_card`: Memory converted from `n` distinct-image records has exactly `n` stored values.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.SampledTableMemory
open DistinctImageTable
variable {S R : Type} [DecidableEq R]

/-- The indexed read-only table obtained by reading the entries of a length-indexed record
collection. -/
def memory {F : S → R} {n : ℕ} (s : Records F n) :
    ReadOnlyTable.Memory (X := S) (R := R) n :=
  fun i => s.entries.get ⟨i.val, by rw [s.length_eq]; exact i.isLt⟩

omit [DecidableEq R] in

/-- Every indexed memory entry belongs to the original record list. -/
theorem memory_mem {F : S → R} {n : ℕ} (s : Records F n) (i : Fin n) :
    memory s i ∈ s.entries := by
  exact List.get_mem _ _

omit [DecidableEq R] in

/-- Every record in the original list occurs at some index of the converted table memory. -/
theorem mem_memory {F : S → R} {n : ℕ} (s : Records F n) (p : S × R)
    (hp : p ∈ s.entries) : ∃ i, memory s i = p := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  refine ⟨⟨i.val, by simpa only [s.length_eq] using i.isLt⟩, ?_⟩
  exact hi

/-- Converting records to memory preserves their finite set of stored values. -/
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

/-- Every converted memory record stores the correct `F`-value of its input
[BrassardHoyerTapp1998Collision]. -/
theorem memory_accurate {F : S → R} {n : ℕ} (s : Records F n) (i : Fin n) :
    (memory s i).2 = F (memory s i).1 := s.accurate _ (memory_mem s i)

/-- Memory converted from `n` distinct-image records has exactly `n` stored values. -/
theorem memory_card {F : S → R} {n : ℕ} (s : Records F n) :
    (ReadOnlyTable.values (memory s)).card = n := by
  rw [memory_values, values_card]

end Qatlib.Papers.CollisionProb97.MainResults.SampledTableMemory
