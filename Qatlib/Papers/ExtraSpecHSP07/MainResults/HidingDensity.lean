/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.StateDefs
import Qatlib.Papers.ExtraSpecHSP07.MainResults.GoodVectorCount
import Qatlib.Papers.ExtraSpecHSP07.MainResults.Reduction
set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

namespace SheetData

variable {G : Type*} [Group G] {p : ℕ} (S : SheetData G p)

theorem hiding_of_good {W : WeylData G p} (hz : S.z = W.z)
    {a : Fin 4 → G} {u : Fin 4 → ZMod p} (hgood : IsGoodVector p u) :
    ∃ j : Fin 4 → (ZMod p)ˣ, IsHidingFamily S.HZ (fun g => S.Psi W a u j g) := by
  obtain ⟨j, hwit⟩ := hgood
  exact ⟨j, S.hiding_of_appropriate hz (S.appropriate_of_witness hz hwit)⟩

theorem HZ_eq_sup {W : WeylData G p} (hz : S.z = W.z) :
    S.HZ = S.H ⊔ commutator G := by
  apply le_antisymm
  · rintro x ⟨h, hh, k, rfl⟩
    have hz' : S.z ^ k ∈ commutator G := by
      have hmem : S.z ^ k ∈ Subgroup.zpowers S.z :=
        Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      simpa [hz, ← W.comm_eq] using hmem
    exact Subgroup.mul_mem_sup hh hz'
  · exact sup_le S.H_le_HZ S.comm_le

noncomputable def hidesSet (S : SheetData G p) (W : WeylData G p) (a : Fin 4 → G) :
    Finset (Fin 4 → ZMod p) := by
  classical
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  exact Finset.univ.filter (fun u => ∃ j : Fin 4 → (ZMod p)ˣ,
    IsHidingFamily S.HZ (fun g => S.Psi W a u j g))

@[simp] theorem mem_hidesSet {W : WeylData G p} {a : Fin 4 → G} {u : Fin 4 → ZMod p} :
    u ∈ S.hidesSet W a ↔ ∃ j : Fin 4 → (ZMod p)ˣ,
      IsHidingFamily S.HZ (fun g => S.Psi W a u j g) := by
  classical
  simp [hidesSet]

theorem goodSet_subset_hidesSet {W : WeylData G p} (hz : S.z = W.z)
    (a : Fin 4 → G) [NeZero p] : goodSet p ⊆ S.hidesSet W a := by
  intro u hu
  rw [mem_goodSet] at hu
  rw [mem_hidesSet]
  exact S.hiding_of_good hz hu

theorem hiding_density {W : WeylData G p} (hz : S.z = W.z) (a : Fin 4 → G) :
    ((p - 9 : ℕ) : ℚ) / (2 * (p : ℚ)) ≤
      ((S.hidesSet W a).card : ℚ) / ((p : ℚ) ^ 4) := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  have hcard : (goodSet p).card ≤ (S.hidesSet W a).card :=
    Finset.card_le_card (S.goodSet_subset_hidesSet hz a)
  have hQ : ((goodSet p).card : ℚ) / ((p : ℚ) ^ 4) ≤
      ((S.hidesSet W a).card : ℚ) / ((p : ℚ) ^ 4) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hcard
  exact le_trans (lemma7_probability W.odd) hQ

theorem theorem2_recovers {W : WeylData G p} (hz : S.z = W.z)
    {a : Fin 4 → G} {u : Fin 4 → ZMod p} {σ : Type*} {f : G → σ}
    (hf : IsHidingFamily S.H f) (hgood : IsGoodVector p u) :
    (∃ j : Fin 4 → (ZMod p)ˣ,
        IsHidingFamily (S.H ⊔ commutator G) (fun g => S.Psi W a u j g)) ∧
      {g : G | g ∈ S.H ⊔ commutator G ∧ f g = f 1} = (S.H : Set G) := by
  have hset : {g : G | g ∈ S.H ⊔ commutator G ∧ f g = f 1} = (S.H : Set G) := by
    ext g
    exact ⟨fun h => (hf.mem_iff g).mp h.2,
      fun h => ⟨Subgroup.mem_sup_left h, (hf.mem_iff g).mpr h⟩⟩
  refine ⟨?_, hset⟩
  obtain ⟨j, hj⟩ := S.hiding_of_good hz (a := a) hgood
  exact ⟨j, (S.HZ_eq_sup hz) ▸ hj⟩

end SheetData

end Qatlib.Papers.ExtraSpecHSP07.MainResults
