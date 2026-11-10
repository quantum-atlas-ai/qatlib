/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

open scoped Pointwise commutatorElement BigOperators

variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_bot_or_eq_top_of_le {p : ℕ} (hE : IsExtraspecial G p)
    {K : Subgroup G} (hK : K ≤ commutator G) : K = ⊥ ∨ K = commutator G := by
  haveI : Fact (Nat.card ↥(commutator G)).Prime :=
    ⟨by rw [hE.commutator_card]; exact hE.prime⟩
  have h := Subgroup.eq_bot_or_eq_top_of_prime_card (G := ↥(commutator G))
    (K.subgroupOf (commutator G))
  rcases h with hbot | htop
  · left
    have hdis : Disjoint K (commutator G) := Subgroup.subgroupOf_eq_bot.mp hbot
    have hinf : K ⊓ commutator G = ⊥ := disjoint_iff.mp hdis
    rwa [inf_eq_left.mpr hK] at hinf
  · right
    have hle : commutator G ≤ K := Subgroup.subgroupOf_eq_top.mp htop
    exact le_antisymm hK hle

theorem inf_commutator_eq_bot_of_not_le {p : ℕ} (hE : IsExtraspecial G p) {H : Subgroup G}
    (h : ¬ commutator G ≤ H) : H ⊓ commutator G = ⊥ := by
  rcases commutator_eq_bot_or_eq_top_of_le hE
      (inf_le_right : H ⊓ commutator G ≤ commutator G) with hb | ht
  · exact hb
  · exact absurd (ht ▸ (inf_le_left : H ⊓ commutator G ≤ H)) h

theorem isMulCommutative_of_inf_commutator_eq_bot {p : ℕ} (hE : IsExtraspecial G p)
    {H : Subgroup G} (hdis : H ⊓ commutator G = ⊥) : IsMulCommutative ↥H := by
  refine IsMulCommutative.of_comm (fun x y => Subtype.ext ?_)
  have hmem : ⁅(x : G), (y : G)⁆ ∈ H ⊓ commutator G := by
    constructor
    · exact Subgroup.commutator_le_self H
        (Subgroup.commutator_mem_commutator x.2 y.2)
    · have hmem' : ⁅(x : G), (y : G)⁆ ∈ ⁅(⊤ : Subgroup G), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top (x : G))
          (Subgroup.mem_top (y : G))
      simpa [commutator] using hmem'
  rw [hdis] at hmem
  have hone : ⁅(x : G), (y : G)⁆ = 1 := by simpa using hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hone

theorem isMulCommutative_sup_commutator {p : ℕ} (hE : IsExtraspecial G p) {H : Subgroup G}
    (hdis : H ⊓ commutator G = ⊥) : IsMulCommutative ↥(H ⊔ commutator G) := by
  have hH : IsMulCommutative ↥H := isMulCommutative_of_inf_commutator_eq_bot hE hdis
  haveI := hH
  haveI : (commutator G).Normal := inferInstance
  refine IsMulCommutative.of_comm (fun x y => Subtype.ext ?_)
  have hx : (x : G) ∈ (H : Set G) * (commutator G : Set G) := by
    rw [← Subgroup.mul_normal H (commutator G)]
    exact x.2
  have hy : (y : G) ∈ (H : Set G) * (commutator G : Set G) := by
    rw [← Subgroup.mul_normal H (commutator G)]
    exact y.2
  obtain ⟨a, ha, z, hz, hxz⟩ := Set.mem_mul.mp hx
  obtain ⟨b, hb, w, hw, hyw⟩ := Set.mem_mul.mp hy
  change (x : G) * (y : G) = (y : G) * (x : G)
  rw [← hxz, ← hyw]
  have hzc : z ∈ Subgroup.center G := by rw [← hE.commutator_eq_center]; exact hz
  have hwc : w ∈ Subgroup.center G := by rw [← hE.commutator_eq_center]; exact hw
  have haz : Commute a z := (commute_iff_eq a z).mpr (Subgroup.mem_center_iff.mp hzc a)
  have haw : Commute a w := (commute_iff_eq a w).mpr (Subgroup.mem_center_iff.mp hwc a)
  have hzb : Commute z b := (commute_iff_eq z b).mpr (Subgroup.mem_center_iff.mp hzc b).symm
  have hzw : Commute z w := (commute_iff_eq z w).mpr (Subgroup.mem_center_iff.mp hzc w).symm
  have hab : Commute a b := (commute_iff_eq a b).mpr (setLike_mul_comm ha hb)
  exact (Commute.mul_right (Commute.mul_left hab hzb) (Commute.mul_left haw hzw)).eq

theorem setOf_mem_of_hiding {H : Subgroup G} {σ : Type*} {f : G → σ}
    (hf : IsHidingFamily H f) {K : Subgroup G} (hK : H ≤ K) :
    {g : G | g ∈ K ∧ f g = f 1} = (H : Set G) := by
  ext g
  exact ⟨fun h => (hf.mem_iff g).mp h.2, fun h => ⟨hK h, (hf.mem_iff g).mpr h⟩⟩

theorem commutator_le_iff_hiding_eq_one {p : ℕ} (hE : IsExtraspecial G p) {H : Subgroup G}
    {σ : Type*} {f : G → σ} (hf : IsHidingFamily H f) {z : G}
    (hz : commutator G = Subgroup.zpowers z) :
    commutator G ≤ H ↔ f z = f 1 := by
  rw [hz]
  constructor
  · intro h
    exact (hf.mem_iff z).mpr (h (Subgroup.mem_zpowers z))
  · intro h
    exact Subgroup.zpowers_le.mpr ((hf.mem_iff z).mp h)

theorem lemma1_finding_H_reduces_to_HG' {p : ℕ} (hE : IsExtraspecial G p) {H : Subgroup G}
    {σ : Type*} {f : G → σ} (hf : IsHidingFamily H f) {z : G}
    (hz : commutator G = Subgroup.zpowers z) :
    (commutator G ≤ H ↔ f z = f 1) ∧
      (commutator G ≤ H → H ⊔ commutator G = H) ∧
      (¬ commutator G ≤ H →
        H ⊓ commutator G = ⊥ ∧ IsMulCommutative ↥(H ⊔ commutator G)) ∧
      (∀ K : Subgroup G, K = H ⊔ commutator G →
        {g : G | g ∈ K ∧ f g = f 1} = (H : Set G)) := by
  refine ⟨commutator_le_iff_hiding_eq_one hE hf hz, ?_, ?_, ?_⟩
  · intro h
    exact sup_eq_left.mpr h
  · intro h
    exact ⟨inf_commutator_eq_bot_of_not_le hE h,
      isMulCommutative_sup_commutator hE (inf_commutator_eq_bot_of_not_le hE h)⟩
  · intro K hK
    rw [hK]
    exact setOf_mem_of_hiding hf le_sup_left

theorem lemma2_abelianization_preimage (H : Subgroup G) :
    (Subgroup.map (abelianizationMap G) H).comap (abelianizationMap G) = H ⊔ commutator G ∧
      Subgroup.map (abelianizationMap G) (H ⊔ commutator G) =
        Subgroup.map (abelianizationMap G) H := by
  refine ⟨comap_map_abelianizationMap G H, ?_⟩
  have hbot : Subgroup.map (abelianizationMap G) (commutator G) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker]
    simpa [abelianizationMap, QuotientGroup.ker_mk'] using hx
  rw [Subgroup.map_sup, hbot, sup_bot_eq]

theorem lemma3_hiding_transfer {H : Subgroup G} {σ : Type*} {ψ : G → σ}
    (hψ : IsHidingFamily (H ⊔ commutator G) ψ) :
    ∃ ψbar : Abelianization G → σ,
      IsHidingFamily (Subgroup.map (abelianizationMap G) H) ψbar := by
  classical
  refine ⟨fun q => ψ (Quotient.out q), fun q q' => ?_⟩
  have hout : ∀ q : Abelianization G, abelianizationMap G (Quotient.out q) = q := by
    intro q
    rw [abelianizationMap, QuotientGroup.mk'_apply]
    exact Quotient.out_eq q
  rw [hψ (Quotient.out q) (Quotient.out q'), ← comap_map_abelianizationMap G H,
    Subgroup.mem_comap, map_mul, map_inv, hout, hout]

theorem theorem1_reduction {H : Subgroup G}
    {σ : Type*} {f : G → σ} (hf : IsHidingFamily H f) {τ : Type*} {ψ : G → τ}
    (hψ : IsHidingFamily (H ⊔ commutator G) ψ) :
    (∃ ψbar : Abelianization G → τ,
        IsHidingFamily (Subgroup.map (abelianizationMap G) H) ψbar) ∧
      {g : G | g ∈ H ⊔ commutator G ∧ f g = f 1} = (H : Set G) :=
  ⟨lemma3_hiding_transfer hψ, setOf_mem_of_hiding hf le_sup_left⟩

theorem corollary1_of_commutator_le {H : Subgroup G}
    {τ : Type*} {ψ : G → τ} (hψ : IsHidingFamily H ψ) (hGH : commutator G ≤ H) :
    H ⊔ commutator G = H ∧
      (∃ ψbar : Abelianization G → τ,
        IsHidingFamily (Subgroup.map (abelianizationMap G) H) ψbar) := by
  have hsup : H ⊔ commutator G = H := sup_eq_left.mpr hGH
  have hψ' : IsHidingFamily (H ⊔ commutator G) ψ := by rw [hsup]; exact hψ
  exact ⟨hsup, lemma3_hiding_transfer hψ'⟩

end Qatlib.Papers.ExtraSpecHSP07.MainResults
