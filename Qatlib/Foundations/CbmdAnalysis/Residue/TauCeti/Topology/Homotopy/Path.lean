/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.UnitInterval

import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Path restrictions, subdivisions, and homotopies

Develops codomain restrictions, initial segments, finite subdivisions, and concatenation
identities for paths and their homotopy classes. `IsPathHomotopyTrivial` expresses ambient
homotopy uniqueness for paths in a subset, and `Path.Homotopic.trans_of_subpath_trans` combines
homotopies along a finite subdivision.

These path tools support the topological contour framework associated with [WangEtAl2026].

## Main statements

* `codRestrict`: Restricts a path's codomain to a subset containing its entire image, with
  endpoints viewed in the subset.
* `exists_partition_with_property`: Local open neighborhoods satisfying a set property along a
  path yield a finite unit-interval partition whose pieces map into such neighborhoods.
* `IsPathHomotopyTrivial`: The property that any two paths with the same endpoints and ranges in
  `U` are homotopic in the ambient space.
* `Path.Homotopic.trans_of_subpath_trans`: Homotopies on consecutive subpath rectangles combine
  into a homotopy between the full paths joined to their endpoint connecting paths.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open scoped _root_.unitInterval
open Topology _root_.Set

/-- In the path-homotopy quotient, composing consecutive subpaths equals the subpath joining
their outer endpoints. -/
@[simp] theorem Path.Homotopic.mk_subpath_trans_mk_subpath
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (a b c : unitInterval) :
    (Path.Homotopic.Quotient.mk (p.subpath a b)).trans
      (Path.Homotopic.Quotient.mk (p.subpath b c)) =
        Path.Homotopic.Quotient.mk (p.subpath a c) := by
  rw [← Path.Homotopic.Quotient.mk_trans]
  exact Path.Homotopic.Quotient.eq.mpr ⟨Path.Homotopy.subpathTransSubpath p a b c⟩

namespace Path
open _root_.Path
variable {X : Type*} [TopologicalSpace X]

/-- Restricts a path's codomain to a subset containing its entire image, with endpoints viewed
in the subset. -/
def codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    Path x y where
  toFun := s.codRestrict γ hmem
  continuous_toFun := γ.continuous.codRestrict hmem
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- Evaluating a codomain-restricted path and coercing to the ambient space recovers the
original path. -/
@[simp]
theorem codRestrict_coe {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) (t : I) :
    ((Path.codRestrict γ) hmem t : X) = γ t := by
  rfl

/-- Mapping a codomain-restricted path by subtype inclusion recovers the original path. -/
@[simp]
theorem map_codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    ((Path.codRestrict γ) hmem).map continuous_subtype_val = γ := by
  ext t
  simp

/-- Mapping a constant path by a continuous function gives the constant path at the image point. -/
@[simp]
theorem map_refl {Y : Type*} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (a : X) :
    (Path.refl a).map hf = Path.refl (f a) :=
  rfl

/-- On the first half of a concatenated path, evaluation equals evaluation of the first path at
the doubled parameter. -/
theorem trans_apply_of_le {x y z : X} (γ : Path x y) (δ : Path y z) {u : I}
    (hu : (u : ℝ) ≤ 1 / 2) (v : I) (hv : (v : ℝ) = 2 * u) : γ.trans δ u = γ v := by
  rw [trans_apply]
  split_ifs
  exact congrArg γ (Subtype.ext hv.symm)

/-- On the second half of a concatenated path, evaluation equals evaluation of the second path
at parameter `2u - 1`. -/
theorem trans_apply_of_ge {x y z : X} (γ : Path x y) (δ : Path y z) {u : I}
    (hu : 1 / 2 ≤ (u : ℝ)) (v : I) (hv : (v : ℝ) = 2 * u - 1) : γ.trans δ u = δ v := by
  rw [trans_apply]
  split_ifs with h
  · have hu' : (u : ℝ) = 1 / 2 := le_antisymm h hu
    have hv_zero : v = 0 := Subtype.ext (by rw [hv, hu']; norm_num)
    rw [hv_zero, δ.source]
    convert γ.target using 2
    exact Subtype.ext (by norm_num [hu'])
  · exact congrArg δ (Subtype.ext hv.symm)

/-- A subpath stays in `V` when its endpoints lie in a parameter interval on which the original
path stays in `V`. -/
theorem subpath_apply_mem {x y : X} {γ : Path x y} {V : Set X} {lo hi : I}
    (hγ : ∀ t ∈ Icc lo hi, γ t ∈ V) {a b : I} (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) (t : I) :
    γ.subpath a b t ∈ V := by
  obtain ⟨s, hs, hst⟩ : γ.subpath a b t ∈ γ '' uIcc a b :=
    range_subpath γ a b ▸ mem_range_self t
  exact hst ▸ hγ s (uIcc_subset_Icc ha hb hs)

/-- A truncated path has range in `U` when the extended original path maps the truncation
interval into `U`. -/
theorem truncateOfLE_range_subset {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) {U : Set X} (hU : Set.Icc t₀ t₁ ⊆ γ.extend ⁻¹' U) :
    Set.range (γ.truncateOfLE h) ⊆ U := by
  rintro _ ⟨s, rfl⟩
  dsimp [truncateOfLE, truncate]
  apply hU
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

/-- The family of initial paths ending at `γ t`, obtained by stopping the extended path at
parameter `t`. -/
noncomputable def initialSegmentFamily {a b : X} (γ : Path a b) (t : I) :
    Path a (γ t) :=
  (γ.truncate 0 t).cast (by rw [min_eq_left t.2.1, γ.extend_zero]) (γ.extend_apply t.2).symm

/-- Every point of a path lies in the path component of its source. -/
theorem mem_pathComponent {a b : X} (γ : Path a b) (t : I) : γ t ∈ pathComponent a :=
  ⟨(Path.initialSegmentFamily γ) t⟩

/-- A path starting in the path component of `x₀` remains in that component. -/
theorem mem_pathComponent_of_mem {a b x₀ : X} (γ : Path a b) (ha : a ∈ pathComponent x₀)
    (t : I) : γ t ∈ pathComponent x₀ :=
  Joined.mem_pathComponent ((Path.mem_pathComponent γ) t) ha

/-- The initial-segment family is jointly continuous in the stopping parameter and path
parameter. -/
theorem continuous_initialSegmentFamily_uncurry {a b : X} (γ : Path a b) :
    Continuous ↿(initialSegmentFamily γ) := by
  have hincl : Continuous (fun ts : I × I ↦ ((ts.1 : ℝ), ts.2) : I × I → ℝ × I) := by fun_prop
  have htrunc : Continuous (fun ts : I × I ↦ γ.truncate 0 ts.1 ts.2 : I × I → X) :=
    (γ.truncate_const_continuous_family 0).comp hincl
  simpa [initialSegmentFamily] using! htrunc

/-- The initial-segment family evaluates as `γ.extend (min s t)`. -/
@[simp] theorem initialSegmentFamily_apply {a b : X} (γ : Path a b) (t s : I) :
    initialSegmentFamily γ t s = γ.extend (min (s : ℝ) t) := by
  simp [initialSegmentFamily, Path.truncate, max_eq_left s.2.1]

/-- The initial segment stopped at zero is the constant path at the source, with the required
endpoint cast. -/
@[simp] theorem initialSegmentFamily_zero {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 0 = (Path.refl a).cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, γ.extend_zero, Path.refl, min_eq_right s.2.1]

/-- The initial segment stopped at one is the original path, with the required endpoint cast. -/
@[simp] theorem initialSegmentFamily_one {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 1 = γ.cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, min_eq_left s.2.2, γ.extend_apply s.2]

/-- Two paths with the same endpoints lying in a simply connected subset have a homotopy that
stays in that subset. -/
theorem exists_homotopy_forall_mem_of_isSimplyConnected {V : Set X} (hV : IsSimplyConnected V)
    {a b : X} {p q : Path a b} (hp : ∀ t, p t ∈ V) (hq : ∀ t, q t ∈ V) :
    ∃ K : p.Homotopy q, ∀ t x, K (t, x) ∈ V := by
  have := hV.simplyConnectedSpace
  have haV : a ∈ V := p.source ▸ hp 0
  have hbV : b ∈ V := p.target ▸ hp 1
  obtain ⟨h⟩ := SimplyConnectedSpace.paths_homotopic
    (Path.codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) p hp)
    (Path.codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) q hq)

  refine ⟨(h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))).cast
    (Path.map_codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) p hp)
    (Path.map_codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) q hq), fun t x => ?_⟩
  simp

/-- A continuous map on the unit square with the prescribed path edges and fixed endpoint edges
witnesses a homotopy between the two paths. -/
theorem homotopic_of_continuous_square {a b : X} {p q : Path a b} (K : I × I → X)
    (hK_cont : Continuous K) (hK_zero : ∀ s, K (0, s) = p s) (hK_one : ∀ s, K (1, s) = q s)
    (hK_left : ∀ t, K (t, 0) = a) (hK_right : ∀ t, K (t, 1) = b) : p.Homotopic q :=
  ⟨{ toFun := K
     continuous_toFun := hK_cont
     map_zero_left := hK_zero
     map_one_left := hK_one
     prop' := by
       intro t s hs
       rcases hs with rfl | hs
       · exact (hK_left t).trans p.source.symm
       · rw [Set.mem_singleton_iff] at hs
         subst hs
         exact (hK_right t).trans p.target.symm }⟩

/-- A neighborhood cover along a path yields a finite monotone parameter subdivision whose
subpaths each lie in one cover member. -/
theorem exists_monotone_range_subpath_subset {ι : Type*} {U : ι → Set X} {x y : X}
    (γ : Path x y) (hU : ∀ s, ∃ i, γ ⁻¹' U i ∈ 𝓝 s) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I), t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ k : Fin n, ∃ i, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U i := by
  obtain ⟨t, ht0, ht_mono, ⟨N, hN⟩, ht_cover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i ↦ interior (γ ⁻¹' U i))
      (fun i ↦ isOpen_interior)
      (fun s _ ↦ by
        obtain ⟨i, hi⟩ := hU s
        exact mem_iUnion.2 ⟨i, mem_interior_iff_mem_nhds.2 hi⟩)
  refine ⟨N, fun k ↦ t k, by simpa using ht0, by simpa using hN N le_rfl,
    fun a b hab ↦ ht_mono (by simpa using hab), fun k ↦ ?_⟩
  obtain ⟨i, hi⟩ := ht_cover k
  refine ⟨i, ?_⟩
  rw [range_subpath_of_le _ _ _ (ht_mono (by simp))]
  rintro _ ⟨s, hs, rfl⟩
  have hs' : s ∈ γ ⁻¹' U i := interior_subset (hi (by simpa using hs))
  exact hs'

/-- Local open neighborhoods satisfying a set property along a path yield a finite unit-interval
partition whose pieces map into such neighborhoods. -/
theorem exists_partition_with_property {x y : X} (γ : Path x y) (P : Set X → Prop)
    (h : ∀ z ∈ range γ, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ P U) :
    ∃ (n : ℕ) (part : unitInterval.Partition n),
      ∀ i : Fin n, ∃ U : Set X, IsOpen U ∧ P U ∧
        MapsTo γ (Icc (part.t i.castSucc) (part.t i.succ)) U := by
  choose U hU_open hU_mem hU_P using h
  obtain ⟨N, t, ht0, htN, ht_mono, ht_cover⟩ :=
    Path.exists_monotone_range_subpath_subset (U := fun z : range γ ↦ U z.val z.property) γ
      fun s ↦ ⟨⟨γ s, s, rfl⟩, γ.continuous.continuousAt.preimage_mem_nhds
        ((hU_open _ _).mem_nhds (hU_mem _ _))⟩
  refine ⟨N, ⟨t, ht_mono, ht0, htN⟩, fun i ↦ ?_⟩
  obtain ⟨⟨z, hz⟩, h_seg⟩ := ht_cover i
  rw [range_subpath_of_le _ _ _ (ht_mono i.castSucc_le_succ)] at h_seg
  exact ⟨U z hz, hU_open z hz, hU_P z hz, fun s hs ↦ h_seg ⟨s, hs, rfl⟩⟩

end Path

/-- In a locally path-connected space, a monotone subdivision subordinate to open sets has open
path-connected neighborhoods at its vertices, each contained in the adjacent assigned sets. -/
theorem unitInterval.exists_vertex_family {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {n : ℕ} {f : I → X} {t : Fin (n + 1) → I} {U : Fin n → Set X}
    (h_mono : Monotone t)
    (hU_open : ∀ i, IsOpen (U i))
    (hU : ∀ i : Fin n, MapsTo f (Icc (t i.castSucc) (t i.succ)) (U i)) :
    ∃ V : Fin (n + 1) → Set X, (∀ j, IsOpen (V j)) ∧ (∀ j, IsPathConnected (V j)) ∧
      (∀ j, f (t j) ∈ V j) ∧ (∀ i : Fin n, V i.castSucc ⊆ U i) ∧ ∀ i : Fin n, V i.succ ⊆ U i := by
  let W : Fin (n + 1) → Set X := fun j ↦ ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
  have hW_open : ∀ j, IsOpen (W j) := fun j ↦
    isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ hU_open i
  have hfW : ∀ j, f (t j) ∈ W j := by
    intro j
    simp only [W, mem_iInter]
    rintro i (rfl | rfl)
    · exact hU i ⟨le_rfl, h_mono i.castSucc_lt_succ.le⟩
    · exact hU i ⟨h_mono i.castSucc_lt_succ.le, le_rfl⟩
  refine ⟨fun j ↦ pathComponentIn (W j) (f (t j)), fun j ↦ (hW_open j).pathComponentIn _,
    fun j ↦ isPathConnected_pathComponentIn (hfW j), fun j ↦ mem_pathComponentIn_self (hfW j),
    fun i ↦ pathComponentIn_subset.trans ?_, fun i ↦ pathComponentIn_subset.trans ?_⟩
  · exact iInter_subset_of_subset i (iInter_subset _ (Or.inl rfl))
  · exact iInter_subset_of_subset i (iInter_subset _ (Or.inr rfl))

namespace Path
open _root_.Path
variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient
open _root_.Path.Homotopic.Quotient

/-- Reversing a path-homotopy class twice gives the original class. -/
@[simp]
theorem symm_symm {x₀ x₁ : X} (γ : Homotopic.Quotient x₀ x₁) : γ.symm.symm = γ := by
  induction γ using _root_.Path.Homotopic.Quotient.ind with
  | mk γ => exact congrArg mk (Path.symm_symm γ)

/-- The reverse of the constant path-homotopy class is itself. -/
@[simp]
theorem symm_refl (x : X) : (_root_.Path.Homotopic.Quotient.refl x).symm = _root_.Path.Homotopic.Quotient.refl x := by
  rw [← mk_refl, ← mk_symm, Path.refl_symm, mk_refl]

instance instTopologicalSpace (x₀ x : X) :
    TopologicalSpace (Path.Homotopic.Quotient x₀ x) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- A set of path-homotopy classes is open exactly when its preimage under the quotient map is
open. -/
theorem isOpen_iff_preimage_mk {x₀ x₁ : X} {S : Set (Path.Homotopic.Quotient x₀ x₁)} :
    IsOpen S ↔ IsOpen ((Path.Homotopic.Quotient.mk : Path x₀ x₁ →
      Path.Homotopic.Quotient x₀ x₁) ⁻¹' S) :=

  Iff.rfl

/-- Composition of endpoint-cast consecutive subpath classes equals the class of the
endpoint-cast combined subpath. -/
theorem subpath_cast_trans {x y : X} (p : Path x y) (a b c : unitInterval) {x₀ x₁ x₂ : X}
    (h₀ : x₀ = p a) (h₁ : x₁ = p b) (h₂ : x₂ = p c) :
    trans (mk ((p.subpath a b).cast h₀ h₁)) (mk ((p.subpath b c).cast h₁ h₂)) =
      mk ((p.subpath a c).cast h₀ h₂) := by
  subst h₀ h₁ h₂
  simp

/-- The homotopy class of a subpath with equal endpoints is the constant path class. -/
theorem subpath_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpath a a) = _root_.Path.Homotopic.Quotient.refl (p a) := by
  simp only [← mk_refl, eq]
  rw [Path.subpath_self]

/-- The class of the subpath from parameter zero to one is the original path class with its
endpoints cast. -/
theorem subpath_zero_one {x y : X} (p : Path x y) :
    mk (p.subpath 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  rw [Path.subpath_zero_one]

end Homotopic.Quotient

end Path

namespace Path.Homotopic
open _root_.Path.Homotopic
variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- Concatenating a null-homotopic loop before a path gives a path homotopic to the original
path. -/
theorem trans_left_of_nullhomotopic {γ₀ : Path x₀ x₀} {γ₁ : Path x₀ x₁}
    (hγ₀ : γ₀.Homotopic (Path.refl x₀)) : (γ₀.trans γ₁).Homotopic γ₁ :=
  (hcomp hγ₀ (.refl γ₁)).trans (refl_trans γ₁)

/-- Concatenating a null-homotopic loop after a path gives a path homotopic to the original
path. -/
theorem trans_right_of_nullhomotopic {γ₀ : Path x₀ x₁} {γ₁ : Path x₁ x₁}
    (hγ₁ : γ₁.Homotopic (Path.refl x₁)) : (γ₀.trans γ₁).Homotopic γ₀ :=
  (hcomp (.refl γ₀) hγ₁).trans (trans_refl γ₀)

/-- If a path followed by the reverse of another is null-homotopic, the two paths are homotopic. -/
theorem of_trans_symm {γ γ' : Path x₀ x₁}
    (h : (γ.trans γ'.symm).Homotopic (Path.refl x₀)) : γ.Homotopic γ' :=
  (trans_refl γ).symm |>.trans <|
  (hcomp (.refl γ) (symm_trans γ').symm) |>.trans <|
  (trans_assoc γ γ'.symm γ').symm |>.trans <|
  (hcomp h (.refl γ')) |>.trans <|
  refl_trans γ'

/-- Cancels a common final path from a homotopy of concatenations. -/
theorem trans_right_cancel {x₀ x₁ x₂ : X} {γ δ : Path x₀ x₁} {e : Path x₁ x₂}
    (h : (γ.trans e).Homotopic (δ.trans e)) : γ.Homotopic δ := by
  have hγ : ((γ.trans e).trans e.symm).Homotopic γ :=
    (trans_assoc γ e e.symm).trans (trans_right_of_nullhomotopic (trans_symm e))
  have hδ : ((δ.trans e).trans e.symm).Homotopic δ :=
    (trans_assoc δ e e.symm).trans (trans_right_of_nullhomotopic (trans_symm e))
  exact hγ.symm.trans ((h.hcomp (_root_.Path.Homotopic.refl e.symm)).trans hδ)

/-- Cancels a common initial path from a homotopy of concatenations. -/
theorem trans_left_cancel {x₀ x₁ x₂ : X} {e : Path x₀ x₁} {γ δ : Path x₁ x₂}
    (h : (e.trans γ).Homotopic (e.trans δ)) : γ.Homotopic δ := by
  have hγ : (e.symm.trans (e.trans γ)).Homotopic γ :=
    (trans_assoc e.symm e γ).symm.trans (trans_left_of_nullhomotopic (symm_trans e))
  have hδ : (e.symm.trans (e.trans δ)).Homotopic δ :=
    (trans_assoc e.symm e δ).symm.trans (trans_left_of_nullhomotopic (symm_trans e))
  exact hγ.symm.trans (((_root_.Path.Homotopic.refl e.symm).hcomp h).trans hδ)

/-- A loop is null-homotopic if its conjugate by a path is null-homotopic. -/
theorem of_conj_nullhomotopic {x₀ x₁ : X} {α : Path x₀ x₁} {δ : Path x₁ x₁}
    (h : ((α.trans δ).trans α.symm).Homotopic (Path.refl x₀)) :
    δ.Homotopic (Path.refl x₁) :=
  trans_left_cancel ((of_trans_symm h).trans (trans_refl α).symm)

/-- A null-homotopic continuous map sends every loop to a loop homotopic to the constant loop. -/
theorem map_nullhomotopic_of_nullhomotopic {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)}
    (hf : f.Nullhomotopic) {a : X} (γ : Path a a) :
    (γ.map (map_continuous f)).Homotopic (Path.refl (f a)) := by
  obtain ⟨c, ⟨F⟩⟩ := hf
  have key := Path.Homotopic.map_trans_evalAt F γ
  have hconst : γ.map (map_continuous (ContinuousMap.const X c)) = Path.refl c := by ext t; rfl
  rw [hconst] at key
  exact Path.Homotopic.trans_right_cancel
    ((key.trans (Path.Homotopic.trans_refl _)).trans (Path.Homotopic.refl_trans _).symm)

/-- A loop contained in a subset whose inclusion is null-homotopic is null-homotopic in the
ambient space. -/
theorem refl_of_forall_mem_of_nullhomotopic {s : Set X}
    (hs : (ContinuousMap.mk (Subtype.val : s → X) continuous_subtype_val).Nullhomotopic)
    {x : X} (γ : Path x x) (hγ : ∀ t, γ t ∈ s) : γ.Homotopic (Path.refl x) := by
  have hx : x ∈ s := γ.source ▸ hγ 0
  have hmap := map_nullhomotopic_of_nullhomotopic hs
    (Path.codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) γ hγ)
  rwa [Path.map_codRestrict] at hmap

namespace Quotient
open _root_.Path.Homotopic.Quotient
variable {x₀ x₁ : X}

/-- Casting the constant path class along an equality of basepoints gives the constant class at
the new basepoint. -/
@[simp, grind =]
theorem refl_cast {x y : X} (h : y = x) : (_root_.Path.Homotopic.Quotient.refl x).cast h h = _root_.Path.Homotopic.Quotient.refl y := by

  cases h; rfl

/-- Two path-homotopy classes are equal if composing the first with the reverse of the second
gives the constant class. -/
theorem eq_of_trans_symm {γ γ' : _root_.Path.Homotopic.Quotient x₀ x₁}
    (h : _root_.Path.Homotopic.Quotient.trans γ (_root_.Path.Homotopic.Quotient.symm γ') = _root_.Path.Homotopic.Quotient.refl x₀) : γ = γ' := by
  induction γ using _root_.Path.Homotopic.Quotient.ind with | mk γ =>
  induction γ' using _root_.Path.Homotopic.Quotient.ind with | mk γ' =>
  simp only [← mk_trans, ← mk_symm, ← mk_refl] at h
  exact Quotient.sound (Homotopic.of_trans_symm (Quotient.exact h))

end Quotient
end Path.Homotopic

section IsPathHomotopyTrivial

variable {X : Type*} [TopologicalSpace X]

/-- The property that any two paths with the same endpoints and ranges in `U` are homotopic in
the ambient space. -/
def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q

/-- Expands path-homotopy triviality into homotopy of all pairs of paths with common endpoints
and ranges in the set. -/
theorem isPathHomotopyTrivial_def {U : Set X} :
    IsPathHomotopyTrivial U ↔
      ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q :=
  Iff.rfl

/-- Every loop whose range lies in a path-homotopy-trivial set is null-homotopic in the ambient
space. -/
theorem IsPathHomotopyTrivial.nullhomotopic {U : Set X} (hU : IsPathHomotopyTrivial U)
    {x : X} (γ : Path x x) (hγ : range γ ⊆ U) : γ.Homotopic (Path.refl x) :=
  hU γ _ hγ (by simpa using hγ ⟨0, γ.source⟩)

/-- A simply connected subset is path-homotopy trivial in the ambient space. -/
theorem IsSimplyConnected.isPathHomotopyTrivial {U : Set X} (hU : IsSimplyConnected U) :
    IsPathHomotopyTrivial U :=
  isPathHomotopyTrivial_def.mpr fun _ _ _ _ hp hq ↦
    let ⟨K, _⟩ := Path.exists_homotopy_forall_mem_of_isSimplyConnected hU
      (range_subset_iff.1 hp) (range_subset_iff.1 hq)
    ⟨K⟩

end IsPathHomotopyTrivial

section Pasting
variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- The subpath between the first and last vertices of a unit-interval partition represents the
original path class after endpoint casts. -/
private theorem Path.Homotopic.Quotient.cast_mk_subpath_t_zero_t_last {x y : X} (p : Path x y)
    (part : unitInterval.Partition n) (h₁ : x = p (part.t 0)) (h₂ : y = p (part.t (Fin.last n))) :
    (Path.Homotopic.Quotient.mk (p.subpath (part.t 0) (part.t (Fin.last n)))).cast h₁ h₂ =
      Path.Homotopic.Quotient.mk p := by
  revert h₁ h₂
  rw [part.t_zero, part.t_last]
  intro h₁ h₂
  rw [Path.Homotopic.Quotient.subpath_zero_one]
  simp

/-- Homotopies on consecutive subpath rectangles combine into a homotopy between the full paths
joined to their endpoint connecting paths. -/
theorem Path.Homotopic.trans_of_subpath_trans {x y x' y' : X}
    (γ : Path x y) (γ' : Path x' y') (part : unitInterval.Partition n)
    (α : (j : Fin (n + 1)) → Path (γ (part.t j)) (γ' (part.t j)))
    (h_rect : ∀ i : Fin n,
      ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ)).Homotopic
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ)))) :
    (γ.trans ((α (Fin.last n)).cast (by simp) (by simp))).Homotopic
      (((α 0).cast (by simp) (by simp)).trans γ') := by
  open _root_.Path.Homotopic.Quotient Path.Homotopic.Quotient in

  let γ_aux : Fin (n + 1) → Path x y' := fun j ↦
    (((γ.subpath (part.t 0) (part.t j)).trans (α j)).trans
      (γ'.subpath (part.t j) (part.t (Fin.last n)))).cast (by simp) (by simp)
  have h_zero : (γ_aux 0).Homotopic (((α 0).cast (by simp) (by simp)).trans γ') := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [subpath_self, cast_mk_subpath_t_zero_t_last γ' part]
    simp
  have h_last : (γ_aux (Fin.last n)).Homotopic
      (γ.trans ((α (Fin.last n)).cast (by simp) (by simp))) := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [subpath_self, cast_mk_subpath_t_zero_t_last γ part]
    simp
  have h_rect' : ∀ (i : Fin n) {w : X} (q : Path.Homotopic.Quotient (γ' (part.t i.succ)) w),
      (Path.Homotopic.Quotient.mk (γ.subpath (part.t i.castSucc) (part.t i.succ))).trans
          ((Path.Homotopic.Quotient.mk (α i.succ)).trans q) =
        (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
          ((Path.Homotopic.Quotient.mk (γ'.subpath (part.t i.castSucc) (part.t i.succ))).trans
            q) := by
    intro i w q
    rw [← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc]
    rw [← mk_trans, ← mk_trans, Path.Homotopic.Quotient.eq.mpr (h_rect i)]
  have h_step : ∀ i : Fin n, (γ_aux i.succ).Homotopic (γ_aux i.castSucc) := by
    intro i
    apply Path.Homotopic.Quotient.exact
    simp only [γ_aux, mk_trans, mk_cast]
    rw [← Path.Homotopic.mk_subpath_trans_mk_subpath γ (part.t 0) (part.t i.castSucc),
      ← Path.Homotopic.mk_subpath_trans_mk_subpath γ' (part.t i.castSucc) (part.t i.succ)]
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [h_rect']
  have h_chain : ∀ j : Fin (n + 1), (γ_aux j).Homotopic (γ_aux 0) := by
    intro j
    induction j using Fin.induction with
    | zero => exact .refl _
    | succ i ih => exact (h_step i).trans ih
  exact h_last.symm.trans ((h_chain (Fin.last n)).trans h_zero)

end Pasting

end
end Qatlib.Foundations.CbmdAnalysis.Residue
