/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.TablePreparation
import Qatlib.Papers.CollisionProb97.MainResults.TableLookup
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.TableRecords
variable {S X R : Type} [DecidableEq S] [DecidableEq R]

def rows {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k) : List (S × R) :=
  List.ofFn L

omit [DecidableEq S] [DecidableEq R] in

theorem mem_rows {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k) (p : S × R) :
    p ∈ rows L ↔ ∃ i, L i = p := by
  simp [rows, List.mem_ofFn]

omit [DecidableEq S] in

theorem recover_exists {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k)
    (p : X × R) (hp : p.2 ∈ ReadOnlyTable.values L) :
    ∃ s, TableLookup.recover (rows L) p = some (s,p.1) ∧ (s,p.2) ∈ rows L := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  apply TableLookup.recover_exists
  refine ⟨(L i).1, (mem_rows L _).mpr ⟨i, ?_⟩⟩
  exact Prod.ext rfl hi

omit [DecidableEq S] in

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

theorem early_correct (F : S → R) (K : Finset S) (s t : S)
    (h : TableLookup.internal (rows (TablePreparation.loaded F (TablePreparation.inputs K))) = some (s,t)) :
    s ∈ K ∧ t ∈ K ∧ s ≠ t ∧ F s = F t := by
  obtain ⟨hne, z, hs, ht⟩ := TableLookup.internal_sound _ s t h
  obtain ⟨hsK, hzS⟩ := (loaded_mem F K s z).mp hs
  obtain ⟨htK, hzT⟩ := (loaded_mem F K t z).mp ht
  exact ⟨hsK, htK, hne, hzS.symm.trans hzT⟩

omit [Fintype S] in

theorem no_early_injective (F : S → R) (K : Finset S)
    (h : TableLookup.internal (rows (TablePreparation.loaded F (TablePreparation.inputs K))) = none) :
    Set.InjOn F (K : Set S) := by
  intro s hs t ht he
  apply TableLookup.internal_none_unique _ s t (F s) h
  · exact (loaded_mem F K s (F s)).mpr ⟨hs,rfl⟩
  · exact (loaded_mem F K t (F s)).mpr ⟨ht,he⟩

end Collision
end Qatlib.Papers.CollisionProb97.MainResults.TableRecords
