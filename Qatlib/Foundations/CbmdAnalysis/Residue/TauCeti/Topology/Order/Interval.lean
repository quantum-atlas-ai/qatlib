/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Filter Set Topology

namespace TauCeti

theorem uIcc_mem_nhds_of_ne {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {a b t : α} (ht : t ∈ uIcc a b) (ha : t ≠ a) (hb : t ≠ b) :
    uIcc a b ∈ 𝓝 t := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at ht ⊢
    exact Icc_mem_nhds (lt_of_le_of_ne ht.1 ha.symm) (lt_of_le_of_ne ht.2 hb)
  · rw [uIcc_of_ge hab] at ht ⊢
    exact Icc_mem_nhds (lt_of_le_of_ne ht.1 hb.symm) (lt_of_le_of_ne ht.2 ha)

theorem exists_Icc_subset_uIcc_disjoint {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] {a b t : α} {s : Set α}
    (hs : IsClosed s) (ht : t ∈ Ioo (min a b) (max a b)) (hts : t ∉ s) :
    ∃ c d : α, t ∈ Ioo c d ∧ Icc c d ⊆ uIcc a b ∧ Disjoint s (Ioo c d) := by
  have hmem : Ioo (min a b) (max a b) \ s ∈ 𝓝 t := (isOpen_Ioo.sdiff hs).mem_nhds ⟨ht, hts⟩
  obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨_, ht.1⟩ ⟨_, ht.2⟩).mp hmem
  obtain ⟨c, hlc, hct⟩ := exists_between hlt
  obtain ⟨d, htd, hdu⟩ := exists_between htu
  have hcd : Icc c d ⊆ Ioo (min a b) (max a b) \ s :=
    fun x hx => hsub ⟨hlc.trans_le hx.1, hx.2.trans_lt hdu⟩
  refine ⟨c, d, ⟨hct, htd⟩, fun x hx => Icc_min_max.subset (Ioo_subset_Icc_self (hcd hx).1),
    disjoint_right.mpr fun x hx => (hcd (Ioo_subset_Icc_self hx)).2⟩

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsCompact.exists_Icc_between {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [DenselyOrdered α] {K : Set α} {a b : α} (hK : IsCompact K)
    (hne : K.Nonempty) (hKs : K ⊆ Ioo a b) :
    ∃ c d, K ⊆ Ioo c d ∧ Icc c d ⊆ Ioo a b := by
  obtain ⟨m, hmK, hm⟩ := hK.exists_isLeast hne
  obtain ⟨M, hMK, hM⟩ := hK.exists_isGreatest hne
  obtain ⟨c, hac, hcm⟩ := exists_between (hKs hmK).1
  obtain ⟨d, hMd, hdb⟩ := exists_between (hKs hMK).2
  exact ⟨c, d, fun x hx ↦ ⟨hcm.trans_le (hm hx), (hM hx).trans_lt hMd⟩,
    fun x hx ↦ ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩⟩

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Set.OrdConnected.eq_Ici_or_eq_Iic_or_eq_univ
    {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : s.OrdConnected) (hne : s.Nonempty) (hclosed : IsClosed s)
    (hunbounded : ¬(BddBelow s ∧ BddAbove s)) :
    (∃ a, s = Ici a) ∨ (∃ b, s = Iic b) ∨ s = univ := by
  have exists_gt (x : α) (h : ¬BddAbove s) : ∃ y ∈ s, x < y := by
    by_contra! h'
    exact h ⟨x, h'⟩
  have exists_lt (x : α) (h : ¬BddBelow s) : ∃ y ∈ s, y < x := by
    by_contra! h'
    exact h ⟨x, h'⟩
  by_cases hbelow : BddBelow s
  · have habove : ¬BddAbove s := fun h ↦ hunbounded ⟨hbelow, h⟩
    refine Or.inl ⟨sInf s, ?_⟩
    rw [← upperClosure_eq_Ici_csInf hne hbelow hclosed]
    apply Subset.antisymm subset_upperClosure
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hxz⟩ := exists_gt x habove
    exact hs.out hy hz ⟨hyx, hxz.le⟩
  · by_cases habove : BddAbove s
    · refine Or.inr <| Or.inl ⟨sSup s, ?_⟩
      rw [← lowerClosure_eq_Iic_csSup hne habove hclosed]
      apply Subset.antisymm subset_lowerClosure
      rintro x ⟨y, hy, hxy⟩
      obtain ⟨z, hz, hzx⟩ := exists_lt x hbelow
      exact hs.out hz hy ⟨hzx.le, hxy⟩
    · refine Or.inr <| Or.inr <| eq_univ_of_forall fun x ↦ ?_
      obtain ⟨y, hy, hyx⟩ := exists_lt x hbelow
      obtain ⟨z, hz, hxz⟩ := exists_gt x habove
      exact hs.out hy hz ⟨hyx.le, hxz.le⟩

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto
    {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {d : α → β} {p : α} {D : β}
    (hdcont : ContinuousOn d (Ici p))
    (hdmono : StrictMonoOn d (Ici p)) (hdl : Tendsto d atTop (𝓝 D)) :
    d '' Ici p = Ico (d p) D := by
  have hle : ∀ x ∈ Ici p, d x ≤ D := by
    intro x hx
    apply ge_of_tendsto hdl
    filter_upwards [eventually_ge_atTop x] with y hxy
    have hy : y ∈ Ici p := hx.trans hxy
    exact hdmono.monotoneOn hx hy hxy
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxp : p ≤ x := hx
    obtain ⟨x1, hx1⟩ := exists_gt x
    have hx1' : x1 ∈ Ici p := hx.trans hx1.le
    have hlt : d x < D := lt_of_lt_of_le
      (hdmono hx hx1' hx1) (hle x1 hx1')
    exact ⟨hdmono.monotoneOn self_mem_Ici hx hxp, hlt⟩
  · exact isPreconnected_Ici.intermediate_value_Ico self_mem_Ici
      (le_principal_iff.mpr (Ici_mem_atTop p)) hdcont hdl

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
