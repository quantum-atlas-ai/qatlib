/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.TablePreparation
import Qatlib.Papers.CollisionProb97.MainResults.TableLookup

/-!
# Correctness of table record recovery

This module relates indexed read-only memory to the record lists used by lookup and internal
collision detection. It certifies the classical record operations in the collision and claw
constructions of [BrassardHoyerTapp1998Collision].

The theorem `early_correct` validates an internal collision in a loaded table, while
`no_early_injective` supplies the injectivity hypothesis required for marked-set counting when
no collision is found.

## Main statements

* `recover_sound`: For accurate table memory, successful recovery returns a stored input with
  the supplied value and preserves the supplied input component.
* `early_correct`: An internal pair found in a table loaded from `K` consists of distinct
  members of `K` with equal function values.
* `no_early_injective`: If the loaded table has no detected internal collision, `F` is injective
  on `K`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.TableRecords
variable {S X R : Type} [DecidableEq S] [DecidableEq R]

/-- The list of records obtained by enumerating every index of the read-only table memory. -/
def rows {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k) : List (S × R) :=
  List.ofFn L

omit [DecidableEq S] [DecidableEq R] in

/-- A record belongs to `rows L` exactly when it occurs at some memory index. -/
theorem mem_rows {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k) (p : S × R) :
    p ∈ rows L ↔ ∃ i, L i = p := by
  simp [rows, List.mem_ofFn]

omit [DecidableEq S] in

/-- A value occurring in table memory permits recovery of a stored matching input paired with
the supplied input. -/
theorem recover_exists {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k)
    (p : X × R) (hp : p.2 ∈ ReadOnlyTable.values L) :
    ∃ s, TableLookup.recover (rows L) p = some (s,p.1) ∧ (s,p.2) ∈ rows L := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  apply TableLookup.recover_exists
  refine ⟨(L i).1, (mem_rows L _).mpr ⟨i, ?_⟩⟩
  exact Prod.ext rfl hi

omit [DecidableEq S] in

/-- For accurate table memory, successful recovery returns a stored input with the supplied
value and preserves the supplied input component. -/
theorem recover_sound {k : ℕ} (F : S → R)
    (L : ReadOnlyTable.Memory (X := S) (R := R) k)
    (hL : ∀ i, (L i).2 = F (L i).1) (p : X × R) (s : S) (x : X)
    (hr : TableLookup.recover (rows L) p = some (s,x)) :
    F s = p.2 ∧ x = p.1 := by
  unfold TableLookup.recover at hr
  cases hl : TableLookup.lookup (rows L) p.2 (fun _ => true) with
  | none => simp only [hl, Option.map_none] at hr; cases hr
  | some t =>
    have he : (t,p.1) = (s,x) := by simpa only [hl, Option.map_some, Option.some.injEq] using hr
    cases he
    have hm := (TableLookup.lookup_sound (rows L) p.2 (fun _ => true) s hl).1
    obtain ⟨i, hi⟩ := (mem_rows L _).mp hm
    refine ⟨?_, rfl⟩
    simpa only [hi] using (hL i).symm

section Collision
variable [Fintype S]

omit [Fintype S] [DecidableEq R] in

/-- A record occurs in the table loaded from `K` exactly when its input is in `K` and its value
is the corresponding `F`-value. -/
theorem loaded_mem (F : S → R) (K : Finset S) (s : S) (z : R) :
    (s,z) ∈ rows (TablePreparation.loaded F (TablePreparation.inputs K)) ↔ s ∈ K ∧ z = F s := by
  rw [mem_rows]
  constructor
  · rintro ⟨i, hi⟩
    have hs := congrArg Prod.fst hi
    have hz := congrArg Prod.snd hi
    change TablePreparation.inputs K i = s at hs
    change F (TablePreparation.inputs K i) = z at hz
    constructor
    · have hm : s ∈ Finset.univ.image (TablePreparation.inputs K) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hs⟩
      simpa only [TablePreparation.inputs_image] using hm
    · simpa only [hs] using hz.symm
  · rintro ⟨hs, rfl⟩
    have hm : s ∈ Finset.univ.image (TablePreparation.inputs K) := by
      rw [TablePreparation.inputs_image]
      exact hs
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact ⟨i, Prod.ext hi (congrArg F hi)⟩

omit [Fintype S] in

/-- An internal pair found in a table loaded from `K` consists of distinct members of `K` with
equal function values. -/
theorem early_correct (F : S → R) (K : Finset S) (s t : S)
    (h : TableLookup.internal (rows (TablePreparation.loaded F (TablePreparation.inputs K))) = some (s,t)) :
    s ∈ K ∧ t ∈ K ∧ s ≠ t ∧ F s = F t := by
  obtain ⟨hne, z, hs, ht⟩ := TableLookup.internal_sound _ s t h
  obtain ⟨hsK, hzS⟩ := (loaded_mem F K s z).mp hs
  obtain ⟨htK, hzT⟩ := (loaded_mem F K t z).mp ht
  exact ⟨hsK, htK, hne, hzS.symm.trans hzT⟩

omit [Fintype S] in

/-- If the loaded table has no detected internal collision, `F` is injective on `K`. -/
theorem no_early_injective (F : S → R) (K : Finset S)
    (h : TableLookup.internal (rows (TablePreparation.loaded F (TablePreparation.inputs K))) = none) :
    Set.InjOn F (K : Set S) := by
  intro s hs t ht he
  apply TableLookup.internal_none_unique _ s t (F s) h
  · exact (loaded_mem F K s (F s)).mpr ⟨hs,rfl⟩
  · exact (loaded_mem F K t (F s)).mpr ⟨ht,he⟩

end Collision
end Qatlib.Papers.CollisionProb97.MainResults.TableRecords
