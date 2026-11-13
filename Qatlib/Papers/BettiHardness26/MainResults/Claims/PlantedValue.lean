/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BettiHardness26.MainResults.Topology.CliqueComplexHomology

set_option backward.isDefEq.respectTransparency false

/-!
# Planted Clique Cycle Lower Bound for Skeleton Betti Numbers

This module proves the deterministic combinatorial core of Lemma 4.2: when a simple
graph `G` contains a `(k - 1)`-simplex (`k`-clique) `σ` in its clique complex `X(G)`,
its oriented boundary `∂σ` forms a nonzero `(k - 2)`-cycle in `skel_{k - 2} X(G)`,
yielding `1 ≤ β_{k - 2}(skel_{k - 2} X(G))`.

## Main statements

* `lemma_4_2`: a maximal `(k - 1)`-simplex witnesses `1 ≤ bettiNumber G (k - 2)`.

## References

* [Strelchuk, Subramanian, and Wesolowski, 2026][StrelchukSubramanianWesolowski2026],
  Lemma 4.2, Section 4, p. 10.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Claims

open Qatlib.Papers.BettiHardness26.MainResults.Topology

variable {V : Type*}

-- On lists, the alternating boundary satisfies the usual cone identity. Mapping sorted
-- lists to their vertex sets then gives the boundary identity used by the cycle space.
private def prepend (v : V) : (List V →₀ ℝ) →ₗ[ℝ] (List V →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (List.cons v)

private def listBoundary : List V → (List V →₀ ℝ)
  | [] => 0
  | v :: l => Finsupp.single l 1 - prepend v (listBoundary l)

private def listBoundaryMap : (List V →₀ ℝ) →ₗ[ℝ] (List V →₀ ℝ) :=
  Finsupp.linearCombination ℝ listBoundary

private lemma listBoundaryMap_prepend (v : V) (c : List V →₀ ℝ) :
    listBoundaryMap (prepend v c) = c - prepend v (listBoundaryMap c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; abel
  | single l a =>
    simp [prepend, listBoundaryMap, listBoundary, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, smul_sub]

private lemma listBoundaryMap_boundary (l : List V) :
    listBoundaryMap (listBoundary l) = 0 := by
  induction l with
  | nil => simp [listBoundary]
  | cons v l ih =>
    rw [listBoundary, map_sub, listBoundaryMap_prepend, ih, map_zero, sub_zero,
      show listBoundaryMap (Finsupp.single l 1) = listBoundary l by
        simp [listBoundaryMap]]
    exact sub_self _

private lemma listBoundary_eq_sum [DecidableEq V] (l : List V) (hn : l.Nodup) :
    listBoundary l = (l.zipIdx.map (fun p : V × ℕ =>
      Finsupp.single (l.erase p.1) ((-1 : ℝ) ^ p.2))).sum := by
  induction l with
  | nil => simp [listBoundary]
  | cons v l ih =>
    rw [listBoundary, ih hn.of_cons, map_list_sum]
    simp only [List.zipIdx_cons', List.map_cons, List.map_map, List.sum_cons,
      List.erase_cons_head, pow_zero]
    rw [sub_eq_add_neg, List.sum_neg, List.map_map]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hvp : v ≠ p.1 := by
      intro h
      exact hn.notMem (h.symm ▸ List.fst_mem_of_mem_zipIdx hp)
    simp [Function.comp_def, prepend, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, List.erase_cons, hvp, pow_succ]

private def toFinsetMap [DecidableEq V] : (List V →₀ ℝ) →ₗ[ℝ] ((Finset V) →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (List.toFinset : List V → Finset V)

private lemma listBoundary_toFinset [DecidableEq V] [LinearOrder V] (l : List V)
    (hn : l.Nodup) (hs : l.Pairwise (· ≤ ·)) :
    toFinsetMap (listBoundary l) = simplexBoundary l.toFinset := by
  rw [listBoundary_eq_sum l hn, map_list_sum]
  unfold simplexBoundary
  rw [(List.toFinset_sort (· ≤ ·) hn).2 hs]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, toFinsetMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  congr 1
  ext w
  simp [hn.mem_erase_iff]

private lemma listBoundary_support [DecidableEq V] (l : List V)
    {t : List V} (ht : t ∈ (listBoundary l).support) : t.Sublist l := by
  induction l generalizing t with
  | nil => simp [listBoundary] at ht
  | cons v l ih =>
    have ht' := Finsupp.support_sub ht
    rcases Finset.mem_union.mp ht' with hsingle | hprepend
    · have ht_eq : t = l := by simpa using hsingle
      subst t
      exact List.sublist_cons_self v l
    · change t ∈ (Finsupp.mapDomain (List.cons v) (listBoundary l)).support at hprepend
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hprepend)
      exact List.Sublist.cons_cons v (ih hu)

section

variable [DecidableEq V] [LinearOrder V]

private lemma boundaryMap_simplexBoundary (σ : Finset V) :
    boundaryMap (simplexBoundary σ) = 0 := by
  let l := σ.sort (· ≤ ·)
  have hnd : l.Nodup := σ.sort_nodup (· ≤ ·)
  have hsorted : l.Pairwise (· ≤ ·) := σ.pairwise_sort (· ≤ ·)
  have hσ : l.toFinset = σ := σ.sort_toFinset (· ≤ ·)
  rw [← hσ, ← listBoundary_toFinset l hnd hsorted]
  change Finsupp.linearCombination ℝ simplexBoundary
    (Finsupp.mapDomain List.toFinset (listBoundary l)) = 0
  rw [Finsupp.linearCombination_mapDomain]
  have hcomm : Finsupp.linearCombination ℝ (simplexBoundary ∘ List.toFinset)
      (listBoundary l) = toFinsetMap (listBoundaryMap (listBoundary l)) := by
    rw [listBoundaryMap, Finsupp.apply_linearCombination]
    simp only [Finsupp.linearCombination_apply]
    apply Finsupp.sum_congr
    intro t ht
    have hsub := listBoundary_support l ht
    rw [Function.comp_apply, Function.comp_apply,
      listBoundary_toFinset t (hnd.sublist hsub) (hsorted.sublist hsub)]
  rw [hcomm, listBoundaryMap_boundary, map_zero]

private lemma simplexBoundary_ne_zero (σ : Finset V) (hσ : σ.Nonempty) :
    simplexBoundary σ ≠ 0 := by
  have hlen : 0 < (σ.sort (· ≤ ·)).length := by simpa using Finset.card_pos.mpr hσ
  obtain ⟨v, l, hsort⟩ : ∃ v l, σ.sort (· ≤ ·) = v :: l :=
    List.exists_cons_of_ne_nil (by intro hs; simp [hs] at hlen)
  have hv : v ∈ σ := (Finset.mem_sort (· ≤ ·)).mp (by simp [hsort])
  have hnodup : (v :: l).Nodup := hsort ▸ σ.sort_nodup (· ≤ ·)
  have htail :
      ((l.zipIdx 1).map (fun p : V × ℕ =>
        Finsupp.single (σ.erase p.1) ((-1 : ℝ) ^ p.2))).sum (σ.erase v) = 0 := by
    change (Finsupp.applyAddHom (σ.erase v) : ((Finset V) →₀ ℝ) →+ ℝ) _ = 0
    rw [map_list_sum, List.map_map]
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨⟨w, i⟩, hwi, rfl⟩ := List.mem_map.mp ha
    have hw : w ∈ l := List.fst_mem_of_mem_zipIdx hwi
    have hne : σ.erase w ≠ σ.erase v := by
      intro heq
      have heq' := (Finset.erase_inj σ hv).mp heq.symm
      exact (List.nodup_cons.mp hnodup).1 (heq' ▸ hw)
    simp [hne]
  have heval : simplexBoundary σ (σ.erase v) = 1 := by
    simp [simplexBoundary, hsort, htail]
  intro hz
  rw [hz] at heval
  simp at heval

end

variable [Fintype V] [DecidableEq V] [LinearOrder V]

private lemma simplexBoundary_mem_span (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k) {σ : Finset V} (hσ : σ ∈ simplices G (k - 1)) :
    simplexBoundary σ ∈ Submodule.span ℝ
      ((↑(simplices G (k - 2)) : Set (Finset V)).image
        (fun τ => Finsupp.single τ (1 : ℝ))) := by
  obtain ⟨hcard, hcl⟩ := (mem_simplices_iff G _ σ).mp hσ
  unfold simplexBoundary
  apply list_sum_mem
  intro c hc
  obtain ⟨⟨v, i⟩, hvi, rfl⟩ := List.mem_map.mp hc
  have hv : v ∈ σ := (Finset.mem_sort (· ≤ ·)).mp (List.fst_mem_of_mem_zipIdx hvi)
  rw [← Finsupp.smul_single_one]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨σ.erase v, ?_, rfl⟩
  rw [Finset.mem_coe, mem_simplices_iff]
  exact ⟨by rw [Finset.card_erase_of_mem hv]; omega, hcl.subset (Finset.erase_subset v σ)⟩

/-- **Lemma 4.2 (Planted value, combinatorial core)**: if `G` contains a `(k - 1)`-simplex `σ`
(a `k`-clique) that is contained in no `k`-simplex, then `1 ≤ bettiNumber G (k - 2)`. -/
theorem lemma_4_2 (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hσ : ∃ σ ∈ simplices G (k - 1), ∀ τ ∈ simplices G k, ¬ σ ⊂ τ) :
    1 ≤ bettiNumber G (k - 2) := by
  obtain ⟨σ, hσ_mem, _⟩ := hσ
  have hcard : σ.card = k := by
    have := ((mem_simplices_iff G (k - 1) σ).mp hσ_mem).1
    omega
  have hnonzero := simplexBoundary_ne_zero σ (Finset.card_pos.mp (by omega))
  have hcycle : simplexBoundary σ ∈ cycleSpace G (k - 2) :=
    ⟨simplexBoundary_mem_span G hk hσ_mem, boundaryMap_simplexBoundary σ⟩
  apply Nat.succ_le_iff.mpr
  change 0 < Module.finrank ℝ (cycleSpace G (k - 2))
  apply (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := cycleSpace G (k - 2))).mpr
  refine ⟨⟨simplexBoundary σ, hcycle⟩, ?_⟩
  intro hz
  exact hnonzero (congrArg Subtype.val hz)

end Qatlib.Papers.BettiHardness26.MainResults.Claims
