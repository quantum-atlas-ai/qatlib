/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamicProg18.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 11 — additivity of the minimum set-cover size over partial covers

The paper's Proposition 11 (p. 13) states that if `P` is a *partial cover* of a
minimum set cover `C ⊆ S` of `U`, i.e. `P = ⋃_{S' ∈ C'} S'` for some
`C' ⊆ C`, then

`f(U, S) = f(P, S) + f(U \ P, S)`

where `f` is the minimum set-cover size.  The Lean statement below takes the
paper's standard set-cover convention that every set of the collection is a
subset of the universe (`hSU`), which is exactly the sentence "a collection
`S` of subsets of an element universe `U`" of Section 2 (p. 4).
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

variable {α : Type} [DecidableEq α]

/-! ## Membership characterisation of the cover-size set -/

/-- `n` is the cardinality of some subfamily of `S` covering `U`. -/
theorem mem_coverCardSet {U : Finset α} {S : Finset (Finset α)} {n : ℕ} :
    n ∈ coverCardSet U S ↔ ∃ C : Finset (Finset α), C ⊆ S ∧ Covers U C ∧ C.card = n := by
  unfold coverCardSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨C, hC, rfl⟩
    rw [Finset.mem_filter] at hC
    exact ⟨C, Finset.mem_powerset.mp hC.1, hC.2, rfl⟩
  · rintro ⟨C, hCS, hCov, rfl⟩
    exact ⟨C, by rw [Finset.mem_filter]; exact ⟨Finset.mem_powerset.mpr hCS, hCov⟩, rfl⟩

/-- Any covering subfamily bounds the minimum cover size from above. -/
theorem minCoverSize_le_card {U : Finset α} {S C : Finset (Finset α)}
    (hCS : C ⊆ S) (hCov : Covers U C) : minCoverSize U S ≤ C.card := by
  unfold minCoverSize
  split_ifs with h
  · exact Finset.min'_le _ _ (mem_coverCardSet.mpr ⟨C, hCS, hCov, rfl⟩)
  · exact absurd ⟨C.card, mem_coverCardSet.mpr ⟨C, hCS, hCov, rfl⟩⟩ h

/-- Whenever some subfamily covers `U`, a minimum cover exists and attains
`minCoverSize`. -/
theorem exists_minCoverSize {U : Finset α} {S : Finset (Finset α)}
    (hne : (coverCardSet U S).Nonempty) :
    ∃ C : Finset (Finset α), C ⊆ S ∧ Covers U C ∧ C.card = minCoverSize U S := by
  unfold minCoverSize
  rw [dif_pos hne]
  have h1 : (coverCardSet U S).min' hne ∈ coverCardSet U S := Finset.min'_mem _ _
  obtain ⟨C, hCS, hCov, hcard⟩ := mem_coverCardSet.mp h1
  exact ⟨C, hCS, hCov, hcard⟩

/-! ## Proposition 11 -/

/-- **Proposition 11, p. 13.**  If `C ⊆ S` is a minimum set cover of `U`
(`C.card = f(U, S)`), `C' ⊆ C` is a subfamily and `P = ⋃ C'` is the
corresponding partial cover, then

`f(U, S) = f(P, S) + f(U \ P, S)`.

The proof follows the paper's argument verbatim: split the minimum cover into
the sets contained in `P` (which cover `P`, because `P` is their union) and the
sets not contained in `P` (which cover `U \ P`); the minimum covers of these
two parts have total size at most `|C|`, and their union is a set cover of `U`,
giving the reverse inequality.

Source: arXiv:1807.05209v1, Proposition 11, page 13. -/
theorem proposition11 {U : Finset α} {S : Finset (Finset α)}
    {C C' : Finset (Finset α)} {P : Finset α}
    (hC : C ⊆ S) (hCov : Covers U C) (hCmin : C.card = minCoverSize U S)
    (hC' : C' ⊆ C) (hP : P = C'.biUnion id)
    (hSU : ∀ S' ∈ S, S' ⊆ U) :
    minCoverSize U S = minCoverSize P S + minCoverSize (U \ P) S := by
  classical
  -- `P` lies inside the universe.
  have hPsub : P ⊆ U := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨S', hS', hxS'⟩ := hx
    exact hSU S' (hC (hC' hS')) hxS'
  -- The two filters of the minimum cover: contained in `P`, respectively not.
  set CP : Finset (Finset α) := C.filter (fun S' => S' ⊆ P) with hCPdef
  set CU : Finset (Finset α) := C.filter (fun S' => ¬ S' ⊆ P) with hCUdef
  have hCPsub : CP ⊆ S := (Finset.filter_subset _ _).trans hC
  have hCUsub : CU ⊆ S := (Finset.filter_subset _ _).trans hC
  -- `CP` covers `P`.
  have hCPcov : Covers P CP := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨S', hS', hxS'⟩ := hx
    refine ⟨S', ?_, hxS'⟩
    rw [hCPdef, Finset.mem_filter]
    refine ⟨hC' hS', ?_⟩
    intro y hy
    rw [hP, Finset.mem_biUnion]
    exact ⟨S', hS', hy⟩
  -- `CU` covers `U \ P`.
  have hCUcov : Covers (U \ P) CU := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxU, hxP⟩ := hx
    obtain ⟨S', hS'C, hxS'⟩ := hCov x hxU
    refine ⟨S', ?_, hxS'⟩
    rw [hCUdef, Finset.mem_filter]
    refine ⟨hS'C, ?_⟩
    intro hsub
    exact hxP (hsub hxS')
  -- Both parts are coverable.
  have hneP : (coverCardSet P S).Nonempty :=
    ⟨CP.card, mem_coverCardSet.mpr ⟨CP, hCPsub, hCPcov, rfl⟩⟩
  have hneQ : (coverCardSet (U \ P) S).Nonempty :=
    ⟨CU.card, mem_coverCardSet.mpr ⟨CU, hCUsub, hCUcov, rfl⟩⟩
  obtain ⟨CP0, hCP0sub, hCP0cov, hCP0card⟩ := exists_minCoverSize hneP
  obtain ⟨CU0, hCU0sub, hCU0cov, hCU0card⟩ := exists_minCoverSize hneQ
  -- Upper bound: the union of the two minimum covers covers `U`.
  have hDsub : CP0 ∪ CU0 ⊆ S := Finset.union_subset hCP0sub hCU0sub
  have hDcov : Covers U (CP0 ∪ CU0) := by
    intro x hxU
    by_cases hxP : x ∈ P
    · obtain ⟨S', hS', hxS'⟩ := hCP0cov x hxP
      exact ⟨S', Finset.mem_union_left _ hS', hxS'⟩
    · have hxQ : x ∈ U \ P := Finset.mem_sdiff.mpr ⟨hxU, hxP⟩
      obtain ⟨S', hS', hxS'⟩ := hCU0cov x hxQ
      exact ⟨S', Finset.mem_union_right _ hS', hxS'⟩
  have hupper : minCoverSize U S ≤ minCoverSize P S + minCoverSize (U \ P) S := by
    have h1 : minCoverSize U S ≤ (CP0 ∪ CU0).card := minCoverSize_le_card hDsub hDcov
    have h2 : (CP0 ∪ CU0).card ≤ CP0.card + CU0.card := Finset.card_union_le _ _
    rw [hCP0card, hCU0card] at h2
    exact h1.trans h2
  -- Lower bound: the two parts of the minimum cover bound the two minima.
  have hCPle : minCoverSize P S ≤ CP.card := minCoverSize_le_card hCPsub hCPcov
  have hCUle : minCoverSize (U \ P) S ≤ CU.card := minCoverSize_le_card hCUsub hCUcov
  have hpartition : CP.card + CU.card = C.card := by
    have hunion : CP ∪ CU = C := by
      rw [hCPdef, hCUdef]
      ext S'
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hsub : S' ⊆ P
        · exact Or.inl ⟨h, hsub⟩
        · exact Or.inr ⟨h, hsub⟩
    have hdisj : Disjoint CP CU := by
      rw [Finset.disjoint_left]
      intro a haCP haCU
      rw [hCPdef, Finset.mem_filter] at haCP
      rw [hCUdef, Finset.mem_filter] at haCU
      exact haCU.2 haCP.2
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hlower : minCoverSize P S + minCoverSize (U \ P) S ≤ minCoverSize U S := by
    rw [← hCmin]
    calc minCoverSize P S + minCoverSize (U \ P) S ≤ CP.card + CU.card :=
          Nat.add_le_add hCPle hCUle
      _ = C.card := hpartition
  exact Nat.le_antisymm hupper hlower

end

end Qatlib.Papers.QDynamicProg18.MainResults
