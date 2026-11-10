/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Irreducible
import Mathlib.SetTheory.Cardinal.Finite
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.PathComponent
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Function _root_.Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace ConnectedComponents
open _root_.ConnectedComponents

variable {G X : Type*} [Monoid G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

noncomputable instance instMulActionOfContinuousConstSMul :
    MulAction G (ConnectedComponents X) where
  smul g := (continuous_const_smul g : Continuous (fun x : X ↦ g • x)).connectedComponentsMap
  one_smul x := by
    obtain ⟨x, rfl⟩ := surjective_coe x
    exact congrArg ConnectedComponents.mk (one_smul G x)
  mul_smul g h x := by
    obtain ⟨x, rfl⟩ := surjective_coe x
    exact congrArg ConnectedComponents.mk (mul_smul g h x)

@[simp]
theorem smul_mk (g : G) (x : X) :
    g • ConnectedComponents.mk x = ConnectedComponents.mk (g • x) := (rfl)

instance : ContinuousConstSMul G (ConnectedComponents X) where
  continuous_const_smul g :=
    (continuous_const_smul g : Continuous (fun x : X ↦ g • x)).connectedComponentsMap_continuous

end ConnectedComponents

namespace ConnectedComponents
open _root_.ConnectedComponents

theorem coe_eq_coe_iff_connectedComponentIn_eq {F : Set X} {a b : X} (ha : a ∈ F) (hb : b ∈ F) :
    ((⟨a, ha⟩ : F) : ConnectedComponents F) = (⟨b, hb⟩ : F) ↔
      connectedComponentIn F a = connectedComponentIn F b := by
  rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb,
    Subtype.val_injective.image_injective.eq_iff, coe_eq_coe]

end ConnectedComponents

namespace Homeomorph
open _root_.Homeomorph

@[simp]
theorem image_connectedComponent {Y : Type*} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    e '' connectedComponent x = connectedComponent (e x) := by
  simpa only [connectedComponentIn_univ, _root_.Set.image_univ_of_surjective e.surjective] using
    e.image_connectedComponentIn (s := _root_.Set.univ) (x := x) (_root_.Set.mem_univ x)

end Homeomorph

namespace TauCeti

theorem connectedComponentIn_inter_eq_sUnion {s U : Set X} {𝒞 : Set (Set X)}
    (hc : ∀ t ∈ 𝒞, IsPreconnected t) (hcover : ⋃₀ 𝒞 = s ∩ U) (x : X) :
    connectedComponentIn s x ∩ U = ⋃₀ {t ∈ 𝒞 | t ⊆ connectedComponentIn s x} := by
  have hsub {t : Set X} (ht : t ∈ 𝒞) : t ⊆ s ∩ U :=
    hcover ▸ subset_sUnion_of_mem ht
  apply Subset.antisymm
  · intro y hy
    have hy' : y ∈ s ∩ U := ⟨connectedComponentIn_subset s x hy.1, hy.2⟩
    obtain ⟨t, ht, hyt⟩ := mem_sUnion.1 (hcover.symm ▸ hy')
    refine mem_sUnion.2 ⟨t, ⟨ht, ?_⟩, hyt⟩
    rw [connectedComponentIn_eq hy.1]
    exact (hc t ht).subset_connectedComponentIn hyt ((hsub ht).trans inter_subset_left)
  · rintro y ⟨t, ⟨ht, htc⟩, hyt⟩
    exact ⟨htc hyt, (hsub ht hyt).2⟩

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.Set.Finite.image_connectedComponentIn_sUnion {s : Set X} {𝒞 : Set (Set X)}
    (h𝒞 : 𝒞.Finite) (hc : ∀ t ∈ 𝒞, IsPreconnected t) (hsub : ⋃₀ 𝒞 ⊆ s) :
    (connectedComponentIn s '' ⋃₀ 𝒞).Finite := by
  rw [sUnion_eq_biUnion, image_iUnion₂]
  refine h𝒞.biUnion fun t ht ↦ Set.Subsingleton.finite ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hts : t ⊆ s := (subset_sUnion_of_mem ht).trans hsub
  exact connectedComponentIn_eq ((hc t ht).subset_connectedComponentIn hx hts hy)

theorem frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X] {F : Set X}
    (hF : IsOpen F) (x : X) : frontier (connectedComponentIn F x) ⊆ Fᶜ := by
  intro y hy hyF
  have hC : IsOpen (connectedComponentIn F x) := hF.connectedComponentIn
  obtain ⟨z, hzy, hzx⟩ :=
    mem_closure_iff.mp hy.1 _ hF.connectedComponentIn (mem_connectedComponentIn hyF)
  have hyC : y ∈ connectedComponentIn F x := by
    rw [connectedComponentIn_eq hzx, ← connectedComponentIn_eq hzy]
    exact mem_connectedComponentIn hyF
  exact hy.2 (by rwa [hC.interior_eq])

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsPreconnected.subset_connectedComponentIn_of_inter_closure_subset
    [LocallyConnectedSpace X] {A U : Set X} {x : X} (hA : IsPreconnected A)
    (hU : IsOpen U) (hxA : x ∈ A) (hxU : x ∈ U)
    (h : A ∩ closure (_root_.connectedComponentIn U x) ⊆ U) :
    A ⊆ _root_.connectedComponentIn U x := by
  refine hA.subset_of_closure_inter_subset hU.connectedComponentIn
    ⟨x, hxA, mem_connectedComponentIn hxU⟩ fun y hy => ?_
  by_contra hyC
  have hfr : y ∈ frontier (_root_.connectedComponentIn U x) :=
    ⟨hy.1, by rwa [hU.connectedComponentIn.interior_eq]⟩
  exact frontier_connectedComponentIn_subset_compl hU x hfr (h ⟨hy.2, hy.1⟩)

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsPreconnected.exists_mem_inter_closure_connectedComponentIn_sdiff
    [LocallyConnectedSpace X] {U S : Set X} {z u : X} (hU : IsPreconnected U)
    (hUS : IsOpen (U \ S)) (hz : z ∈ U \ S) (hu : u ∈ U)
    (huz : u ∉ _root_.connectedComponentIn (U \ S) z) :
    ∃ p ∈ S ∩ U, p ∈ closure (_root_.connectedComponentIn (U \ S) z) := by
  by_contra! h
  exact huz (IsPreconnected.subset_connectedComponentIn_of_inter_closure_subset hU hUS hz.1 hz
    (fun p hp => ⟨hp.1, fun hpS => h p ⟨hpS, hp.1⟩ hp.2⟩) hu)

protected theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsClosed.connectedComponentIn {F : Set X} {x : X} (hF : IsClosed F) :
    IsClosed (connectedComponentIn F x) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  by_cases hx : x ∈ F
  · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset F x) hF) hy
  · rw [connectedComponentIn_eq_empty hx, closure_empty] at hy
    exact hy.elim

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.IsClosed.exists_isOpen_isCompact_closure_disjoint_frontier [T2Space X]
    [LocallyCompactSpace X] {F : Set X} (hF : IsClosed F) {x : X}
    (hx : IsCompact (connectedComponentIn F x)) :
    ∃ V, IsOpen V ∧ connectedComponentIn F x ⊆ V ∧ IsCompact (closure V) ∧
      Disjoint (frontier V) F := by
  by_cases hxF : x ∈ F
  swap
  · exact ⟨∅, isOpen_empty, by simp [connectedComponentIn_eq_empty hxF], by simp, by simp⟩

  obtain ⟨W, hWo, hQW, -, hWc⟩ :=
    exists_open_between_and_isCompact_closure hx isOpen_univ (subset_univ _)
  set Y := F ∩ closure W
  have hxY : x ∈ Y := ⟨hxF, subset_closure (hQW (mem_connectedComponentIn hxF))⟩
  have hQY : connectedComponentIn Y x = connectedComponentIn F x :=
    (connectedComponentIn_mono x inter_subset_left).antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hxF)
        fun y hy => ⟨connectedComponentIn_subset _ _ hy, subset_closure (hQW hy)⟩)
  have : CompactSpace Y := isCompact_iff_compactSpace.mp (hWc.inter_left hF)
  set y : Y := ⟨x, hxY⟩
  have himage : ((↑) : Y → X) '' connectedComponent y = connectedComponentIn F x := by
    rw [← connectedComponentIn_eq_image hxY, hQY]

  obtain ⟨u, hu⟩ := (hWo.preimage continuous_subtype_val).isClosed_compl.isCompact
    |>.elim_finite_subfamily_closed (fun s : {s : Set Y // IsClopen s ∧ y ∈ s} => s.1)
      (fun s => s.2.1.1) (by
        rw [← connectedComponent_eq_iInter_isClopen, disjoint_compl_left_iff_subset]
        exact fun z hz => hQW (himage ▸ mem_image_of_mem _ hz))
  set s : Set Y := ⋂ i ∈ u, i.1
  have hs : IsClopen s := isClopen_biInter_finset fun i _ => i.2.1
  have hsW : s ⊆ (↑) ⁻¹' W := disjoint_compl_left_iff_subset.mp hu
  obtain ⟨O, hOo, hOs⟩ := isOpen_induced_iff.mp hs.isOpen

  obtain ⟨V, hVo, hsV, hVWO, hVc⟩ := exists_open_between_and_isCompact_closure
    (hs.isClosed.isCompact.image continuous_subtype_val) (hWo.inter hOo)
    (image_subset_iff.mpr fun z hz => ⟨hsW hz, by rw [← hOs] at hz; exact hz⟩)
  refine ⟨V, hVo, ?_, hVc, disjoint_left.mpr fun z hz hzF => ?_⟩
  · rw [← himage]
    exact (image_mono (hs.connectedComponent_subset
      (mem_iInter₂.mpr fun i _ => i.2.2))).trans hsV
  · have hzWO := hVWO hz.1
    have hzs : (⟨z, hzF, subset_closure hzWO.1⟩ : Y) ∈ s := by
      rw [← hOs]
      exact hzWO.2
    exact hz.2 (by rw [hVo.interior_eq]; exact hsV ⟨_, hzs, rfl⟩)

theorem connectedComponentIn_eq_of_lt {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] {D H : Set X} {z : X} {φ : X → α} {c : α} (hH : IsPreconnected H)
    (hHD : H ⊆ D) (hz : z ∈ H) (hzc : c < φ z) (hφ : ContinuousOn φ D)
    (hDne : ∀ q ∈ D, φ q ≠ c) (hmem : ∀ q ∈ D, c < φ q → q ∈ H) :
    connectedComponentIn D z = H := by
  apply Subset.antisymm
  · intro q hq
    have hqD : q ∈ D := connectedComponentIn_subset D z hq
    apply hmem q hqD
    rcases lt_or_gt_of_ne (hDne q hqD) with hqlt | hqgt
    · have hzC : z ∈ connectedComponentIn D z := mem_connectedComponentIn (hHD hz)
      obtain ⟨p, hpC, hpc⟩ := isPreconnected_connectedComponentIn.intermediate_value hq hzC
        (hφ.mono (connectedComponentIn_subset D z)) ⟨hqlt.le, hzc.le⟩
      exact (hDne p (connectedComponentIn_subset D z hpC) hpc).elim
    · exact hqgt
  · exact hH.subset_connectedComponentIn hz hHD

theorem connectedComponentIn_compl_Icc_eq_Ioi {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {a b x : α} (hab : a ≤ b)
    (hx : b < x) : connectedComponentIn (Icc a b)ᶜ x = Ioi b := by
  refine Subset.antisymm (fun y hy => ?_)
    (isPreconnected_Ioi.subset_connectedComponentIn hx fun y hy h => not_lt.2 h.2 hy)
  by_contra hyb
  have hya : y < a := not_le.1 fun hay => connectedComponentIn_subset _ _ hy ⟨hay, not_lt.1 hyb⟩
  exact connectedComponentIn_subset _ _ (isPreconnected_connectedComponentIn.Icc_subset hy
    (mem_connectedComponentIn fun h => not_lt.2 h.2 hx) ⟨(hya.trans_le hab).le, hx.le⟩)
    ⟨hab, le_rfl⟩

theorem connectedComponentIn_compl_Icc_eq_Iio {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {a b x : α} (hab : a ≤ b)
    (hx : x < a) : connectedComponentIn (Icc a b)ᶜ x = Iio a := by
  refine Subset.antisymm (fun y hy => ?_)
    (isPreconnected_Iio.subset_connectedComponentIn hx fun y hy h => not_lt.2 h.1 hy)
  by_contra hya
  have hyb : b < y := not_le.1 fun hyb => connectedComponentIn_subset _ _ hy ⟨not_lt.1 hya, hyb⟩
  exact connectedComponentIn_subset _ _ (isPreconnected_connectedComponentIn.Icc_subset
    (mem_connectedComponentIn (show x ∈ (Icc a b)ᶜ from fun h => not_lt.2 h.1 hx)) hy ⟨hx.le, (hab.trans_lt hyb).le⟩)
    ⟨le_rfl, hab⟩

theorem isPreconnected_compl_of_isPreconnected_frontier [LocallyConnectedSpace X]
    [PreconnectedSpace X] {U : Set X} (hU : IsOpen U) (hf : IsPreconnected (frontier U)) :
    IsPreconnected Uᶜ := by

  rcases (frontier U).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rcases frontier_eq_empty_iff.mp h with rfl | rfl
    · simpa using isPreconnected_univ
    · simpa using isPreconnected_empty
  have hpiece : ∀ y, IsPreconnected (frontier U ∪ connectedComponentIn (closure U)ᶜ y) := by
    intro y
    set D := connectedComponentIn (closure U)ᶜ y
    rcases D.eq_empty_or_nonempty with hD | hD
    · simpa [hD] using hf
    have hDu : D ≠ univ := fun h =>
      connectedComponentIn_subset _ _ (h ▸ mem_univ p : p ∈ D) hp.1
    obtain ⟨q, hq⟩ := nonempty_frontier_iff.mpr ⟨hD, hDu⟩
    have hqU : q ∈ frontier U := by
      refine ⟨?_, ?_⟩
      · simpa using frontier_connectedComponentIn_subset_compl isClosed_closure.isOpen_compl y hq
      · rw [hU.interior_eq]
        intro hqU
        obtain ⟨z, hzU, hzD⟩ := mem_closure_iff.mp hq.1 U hU hqU
        exact connectedComponentIn_subset _ _ hzD (subset_closure hzU)
    have hins : IsPreconnected (insert q D) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert q D)
        (insert_subset hq.1 subset_closure)
    have := hf.union' ⟨q, hqU, mem_insert q D⟩ hins
    rwa [union_insert, insert_eq_of_mem (mem_union_left D hqU)] at this
  have hcover : Uᶜ = ⋃ y, frontier U ∪ connectedComponentIn (closure U)ᶜ y := by
    refine Subset.antisymm (fun x hx => mem_iUnion.mpr ⟨x, ?_⟩) (iUnion_subset fun y => ?_)
    · by_cases hxc : x ∈ closure U
      · exact Or.inl (hU.frontier_eq ▸ ⟨hxc, hx⟩)
      · exact Or.inr (mem_connectedComponentIn hxc)
    · refine union_subset (hU.frontier_eq ▸ fun x hx => hx.2) fun x hx hxU => ?_
      exact connectedComponentIn_subset _ _ hx (subset_closure hxU)
  rw [hcover]
  exact isPreconnected_iUnion ⟨p, mem_iInter.mpr fun _ => Or.inl hp⟩ hpiece

theorem isPreconnected_compl_of_isDiscrete [PreconnectedSpace X] {s : Set X} (hs : IsClosed s)
    (hd : IsDiscrete s) (h : ∀ x ∈ s, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x})) :
    IsPreconnected sᶜ := by
  have hV : ∀ x ∈ s, ∃ V ∈ 𝓝 x, V \ {x} ⊆ sᶜ ∧ IsConnected (V \ {x}) := by
    intro x hx
    obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_exists_isOpen.1 hd x hx
    have hxu : x ∈ u := (hus.symm ▸ mem_singleton x : x ∈ u ∩ s).1
    obtain ⟨V, hV, hVu, hc⟩ := h x hx u (hu.mem_nhds hxu)
    refine ⟨V, hV, fun y hy hys ↦ hy.2 ?_, hc⟩
    simpa [← hus] using And.intro (hVu hy.1) hys
  choose! V hVn hVs hVc using hV

  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  have hside (x : X) (hx : x ∈ s) : V x \ {x} ⊆ u ∨ V x \ {x} ⊆ v :=
    isPreconnected_iff_subset_of_disjoint.1 (hVc x hx).isPreconnected u v hu hv
      ((hVs x hx).trans hcov) (subset_empty_iff.1 <| hdisj ▸ inter_subset_inter_left _ (hVs x hx))

  have hext (w : Set X) (hw : IsOpen w) : IsOpen (w \ s ∪ {x | x ∈ s ∧ V x \ {x} ⊆ w}) := by
    refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
    rcases hy with hy | ⟨hys, hyw⟩
    · exact Filter.mem_of_superset ((hw.inter hs.isOpen_compl).mem_nhds hy) subset_union_left
    · refine Filter.mem_of_superset (hVn y hys) fun z hz ↦ ?_
      rcases eq_or_ne z y with rfl | hzy
      · exact Or.inr ⟨hys, hyw⟩
      · exact Or.inl ⟨hyw ⟨hz, hzy⟩, hVs y hys ⟨hz, hzy⟩⟩
  have hnot (x : X) (hx : x ∈ s) (hxu : V x \ {x} ⊆ u) (hxv : V x \ {x} ⊆ v) : False := by
    obtain ⟨z, hz⟩ := (hVc x hx).nonempty
    exact (eq_empty_iff_forall_notMem.1 hdisj) z ⟨hVs x hx hz, hxu hz, hxv hz⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ _ _ (hext u hu) (hext v hv)
    (fun y _ ↦ by
      by_cases hys : y ∈ s
      · exact (hside y hys).imp (fun h ↦ Or.inr ⟨hys, h⟩) fun h ↦ Or.inr ⟨hys, h⟩
      · exact (hcov hys).imp (fun h ↦ Or.inl ⟨h, hys⟩) fun h ↦ Or.inl ⟨h, hys⟩)
    (by
      refine eq_empty_iff_forall_notMem.2 fun y ⟨_, hyu, hyv⟩ ↦ ?_
      rcases hyu with hyu | hyu <;> rcases hyv with hyv | hyv
      · exact (eq_empty_iff_forall_notMem.1 hdisj) y ⟨hyu.2, hyu.1, hyv.1⟩
      · exact (hyu.2 hyv.1).elim
      · exact (hyv.2 hyu.1).elim
      · exact hnot y hyu.1 hyu.2 hyv.2) with h | h
  · exact Or.inl fun y hy ↦ ((h (mem_univ y)).resolve_right fun h' ↦ hy h'.1).1
  · exact Or.inr fun y hy ↦ ((h (mem_univ y)).resolve_right fun h' ↦ hy h'.1).1

instance instT1SpaceConnectedComponents : T1Space (ConnectedComponents X) :=
  ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩

instance instPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    PathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

instance instLocPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    LocallyPathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

noncomputable def connectedComponentsSigmaHomeomorph [LocallyConnectedSpace X] :
    (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ₜ X := by
  let e : (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ X :=
    Equiv.sigmaPreimageEquiv ConnectedComponents.mk
  exact e.toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ ↦ continuous_subtype_val)
    (isOpenMap_sigma.mpr fun C ↦
      ((isOpen_discrete {C}).preimage ConnectedComponents.continuous_coe).isOpenMap_subtype_val)

@[simp]
theorem connectedComponentsSigmaHomeomorph_apply [LocallyConnectedSpace X]
    (z : Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) :
    connectedComponentsSigmaHomeomorph z = z.2 :=
  (rfl)

@[simp]
theorem connectedComponentsSigmaHomeomorph_symm_apply [LocallyConnectedSpace X] (x : X) :
    connectedComponentsSigmaHomeomorph.symm x =
      ⟨ConnectedComponents.mk x, ⟨x, Set.mem_singleton _⟩⟩ :=
  (rfl)

theorem finite_connectedComponents_of_finite_irreducibleComponents
    (h : (irreducibleComponents X).Finite) : Finite (ConnectedComponents X) := by
  let C : Set (ConnectedComponents X) :=
    ⋃ Z ∈ irreducibleComponents X, ConnectedComponents.mk '' Z
  have hC : C.Finite := h.biUnion fun Z hZ =>
    Set.Subsingleton.finite <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [ConnectedComponents.coe_eq_coe']
      exact hZ.1.isConnected.isPreconnected.subset_connectedComponent hy hx
  apply Finite.of_finite_univ
  rw [← Set.eq_univ_of_forall]
  · exact hC
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact Set.mem_biUnion (irreducibleComponent_mem_irreducibleComponents x)
      ⟨x, mem_irreducibleComponent, rfl⟩

theorem isClopen_of_finite_pairwiseDisjoint_closed_cover {ι : Type*} [Finite ι] {U : ι → Set X}
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (Disjoint on U))
    (hunion : ⋃ i, U i = univ) (i : ι) : IsClopen (U i) := by
  refine ⟨hclosed i, ?_⟩
  rw [← isClosed_compl_iff, compl_eq_univ_diff, ← hunion, iUnion_diff]
  refine isClosed_iUnion_of_finite fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hne
  · simp
  · have heq : U j \ U i = U j := by
      ext x
      exact ⟨fun h => h.1, fun hx => ⟨hx, fun hy => Set.disjoint_left.mp (hdisj hne) hx hy⟩⟩
    rw [heq]
    exact hclosed j

theorem natCard_connectedComponents_eq_of_iUnion_eq_univ {ι : Type*} [Finite ι] {U : ι → Set X}
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (Disjoint on U))
    (hunion : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) :
    Nat.card (ConnectedComponents X) = Nat.card ι := by
  have hclopen : ∀ i, IsClopen (U i) :=
    isClopen_of_finite_pairwiseDisjoint_closed_cover hclosed hdisj hunion
  have (i : ι) : Unique (ConnectedComponents (U i)) :=
    have := isPreconnected_iff_preconnectedSpace.1 (hconn i).isPreconnected
    have := (hconn i).nonempty.to_subtype
    uniqueOfSubsingleton (ConnectedComponents.mk (Classical.arbitrary _))
  exact Nat.card_congr ((ConnectedComponents.equivOfIsClopen hclopen hdisj hunion).trans
    (Equiv.sigmaUnique ι _))

end TauCeti

end
end Qatlib.Foundations.CbmdAnalysis.Residue
