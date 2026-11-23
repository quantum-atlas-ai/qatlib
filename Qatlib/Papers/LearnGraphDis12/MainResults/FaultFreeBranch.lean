/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LearnGraphDis12.MainResults.SourceLemma9
public import Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost
import Mathlib.Data.Finset.Card

public section

/-!
# Fault-free children of a learning-graph block

[Belovs2012], Lemma 9 of the [fixed preprint](https://arxiv.org/abs/1205.1534v2).
At a fixed parent of the block decomposition, distinct candidate indices have
distinct representative positions outside the previously loaded certificate
positions. The negative input cannot supply the certificate letter at every
candidate. This gives the nonempty filter required for inclusion–exclusion.
The representative map is supplied at the parent, and the lemma computes the
signed child sum before any construction of the arc matrices.
-/

open scoped BigOperators

namespace Qatlib.Papers.LearnGraphDis12.MainResults

open Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost

/-- In a negative word for `k`-distinctness, every letter occurs at most
`k - 1` times for positive `k`. -/
theorem letter_count_le_of_k_distinctness_eq_false {k n q : ℕ} (hk : 0 < k)
    (y : Fin n → Fin q) (hy : kDistinctness k n q y = false) (letter : Fin q) :
    (Finset.univ.filter fun i => y i = letter).card ≤ k - 1 := by
  by_contra! hcard
  have hkcard : k ≤ (Finset.univ.filter fun i => y i = letter).card := by omega
  obtain ⟨S, hsub, hS⟩ := Finset.exists_subset_card_eq hkcard
  simp only [kDistinctness, decide_eq_false_iff_not] at hy
  exact hy ⟨S, hS, letter, fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩

/-- If the negative input has at most `k - 1` copies of the certificate letter,
at least one of the `k - ℓ - 1` candidate representatives at an interior parent
avoids that letter. The `s - 1` previously loaded positions already carry it. -/
theorem fault_free_representative_exists {I A : Type*} [Fintype I] [DecidableEq A]
    {k ℓ s : ℕ} (hℓs : ℓ + 1 < s) (hsk : s ≤ k)
    (y : I → A) (letter : A) (previous : Finset I) (candidates : Finset ℕ)
    (representative : ℕ → I) (hprevious : previous.card = s - 1)
    (hcandidates : candidates.card = k - ℓ - 1)
    (hinj : Set.InjOn representative (↑candidates : Set ℕ))
    (hfresh : ∀ j ∈ candidates, representative j ∉ previous)
    (hloaded : ∀ i ∈ previous, y i = letter)
    (hmultiplicity : (Finset.univ.filter fun i => y i = letter).card ≤ k - 1) :
    (candidates.filter fun j => y (representative j) ≠ letter).Nonempty := by
  classical
  by_contra h
  have hfault : ∀ j ∈ candidates, y (representative j) = letter := by
    intro j hj
    by_contra hne
    exact h ⟨j, Finset.mem_filter.mpr ⟨hj, hne⟩⟩
  have hdisjoint : Disjoint previous (candidates.image representative) := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi himage
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp himage
    exact hfresh j hj hi
  have hsub : previous ∪ candidates.image representative ⊆
      Finset.univ.filter (fun i => y i = letter) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hloaded i hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact hfault j hj
  have hcard := (Finset.card_le_card hsub).trans hmultiplicity
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injOn hinj,
    hprevious, hcandidates] at hcard
  omega

/-- Under the multiplicity bound, the agreeing children of a parent contribute
its signed value. All nonempty candidate subsets occur in the sum, with the
faulty children assigned zero. -/
theorem fault_filtered_child_sum {I A : Type*} [Fintype I] [DecidableEq A]
    {k ℓ s : ℕ} (hℓs : ℓ + 1 < s) (hsk : s ≤ k)
    (y : I → A) (letter : A) (previous : Finset I) (candidates : Finset ℕ)
    (representative : ℕ → I) (hprevious : previous.card = s - 1)
    (hcandidates : candidates.card = k - ℓ - 1)
    (hinj : Set.InjOn representative (↑candidates : Set ℕ))
    (hfresh : ∀ j ∈ candidates, representative j ∉ previous)
    (hloaded : ∀ i ∈ previous, y i = letter)
    (hmultiplicity : (Finset.univ.filter fun i => y i = letter).card ≤ k - 1)
    (q : ℝ) (prefixSize : ℕ) :
    (∑ D ∈ candidates.powerset.filter Finset.Nonempty,
      if ∀ j ∈ D, y (representative j) ≠ letter then
        (-1 : ℝ) ^ (ℓ + 1 + prefixSize + D.card) * q else 0) =
      (-1 : ℝ) ^ (ℓ + prefixSize) * q := by
  classical
  let good := candidates.filter fun j => y (representative j) ≠ letter
  have hgood : good.Nonempty := fault_free_representative_exists hℓs hsk y letter
    previous candidates representative hprevious hcandidates hinj hfresh hloaded hmultiplicity
  rw [← Finset.sum_filter]
  have hfilter :
      (candidates.powerset.filter Finset.Nonempty).filter
        (fun D => ∀ j ∈ D, y (representative j) ≠ letter) =
      good.powerset.filter Finset.Nonempty := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hsub, hne⟩, hagree⟩
      exact ⟨fun j hj => Finset.mem_filter.mpr ⟨hsub hj, hagree j hj⟩, hne⟩
    · rintro ⟨hsub, hne⟩
      exact ⟨⟨fun j hj => (Finset.mem_filter.mp (hsub hj)).1, hne⟩,
        fun j hj => (Finset.mem_filter.mp (hsub hj)).2⟩
  rw [hfilter]
  exact Qatlib.Papers.LearnGraphDis12.MainResults.SourceLemma9.inclusion_exclusion_step
    q ℓ prefixSize good hgood

end Qatlib.Papers.LearnGraphDis12.MainResults
