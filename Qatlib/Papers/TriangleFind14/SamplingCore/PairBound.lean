/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.PairSample
public import Qatlib.Papers.TriangleFind14.MainResults.SourceLemma43

@[expose] public section


/-!
# Arbitrary-pair sampling in Le Gall's Lemma 4.3

Fixed source: arXiv:1407.0085v2, corpus135, printed pp12–13.
The public proof at Qatlib9eb6a0d832f2 is generalized by the readable
fixed-family counting proof in `ProbabilityCore.Concentration.PairSample`.
No adjacency is required of the distinguished pair.

`lemma43NoEdge` repairs the public API while retaining its edge-filtered
delta model. `lemma43Pairs` instead uses the paper's actual all-unordered-pair
model, preserving the real graph in both common-neighbor conditions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators
open Qatlib.Papers.TriangleFind14.MainResults
open Qatlib.Foundations.ProbabilityCore.Concentration

namespace Qatlib.Papers.TriangleFind14.SamplingCore

/-- The paper's delta family uses all pairs of neighbors of `w`, without an edge filter. -/
def correctDelta {V : Type*}
    (G : SimpleGraph V) (X A : Finset V) (w : V) : Finset (Finset V) :=
  letI := Classical.decRel G.Adj
  ((A.filter (fun v => G.Adj v w)).powersetCard 2).filter
    (fun e => ¬ coveredByX G X e)

/-- On an actual pair, coverage is exactly containment in one real common neighborhood. -/
theorem coverPairIff {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (X e : Finset V) (hc : e.card = 2) :
    coveredByX G X e ↔ ∃ x ∈ X, ∀ v ∈ e, G.Adj x v := by
  constructor
  · rintro ⟨x, hx, u, hu, v, hv, huv, hxu, hxv⟩
    have hsub : ({u, v} : Finset V) ⊆ e :=
      Finset.insert_subset hu (Finset.singleton_subset_iff.2 hv)
    have heq : e = {u, v} :=
      (Finset.eq_of_subset_of_card_le hsub
        (by rw [hc, Finset.card_pair_eq_two_iff.mpr huv])).symm
    refine ⟨x, hx, ?_⟩
    intro z hz
    rw [heq] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxu
    · exact hxv
  · rintro ⟨x, hx, hadj⟩
    obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp hc
    have hu : u ∈ e := by rw [heq]; simp
    have hv : v ∈ e := by rw [heq]; simp
    exact ⟨x, hx, u, hu, v, hv, huv, hadj u hu, hadj v hv⟩

/-- Correct delta membership states all-pair support and the two actual graph conditions. -/
theorem correctMemIff {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (X A : Finset V) (w : V) (e : Finset V) :
    e ∈ correctDelta G X A w ↔
      e ⊆ A ∧ e.card = 2 ∧
        (¬ ∃ x ∈ X, ∀ v ∈ e, G.Adj x v) ∧ ∀ v ∈ e, G.Adj w v := by
  simp only [correctDelta, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hs, hc⟩, hn⟩
    refine ⟨hs.trans (Finset.filter_subset _ _), hc, ?_, ?_⟩
    · intro hcover
      exact hn ((coverPairIff G X e hc).2 hcover)
    · intro v hv
      exact G.adj_symm (Finset.mem_filter.1 (hs hv)).2
  · rintro ⟨hs, hc, hn, hw⟩
    refine ⟨⟨?_, hc⟩, ?_⟩
    · intro v hv
      exact Finset.mem_filter.2 ⟨hs hv, G.adj_symm (hw v hv)⟩
    · intro hcover
      exact hn ((coverPairIff G X e hc).1 hcover)

/-- The retained public delta model consists of supported two-element sets. -/
theorem oldPairs {V : Type*}
    (G : SimpleGraph V) (X A : Finset V) (w : V) :
    ∀ e ∈ deltaSetW G X A w, e ⊆ A ∧ e.card = 2 := by
  intro e he
  unfold deltaSetW at he
  obtain ⟨hs, hc, _⟩ := mem_edgeSetIn (Finset.mem_filter.1 he).1
  exact ⟨hs.trans (Finset.filter_subset _ _), hc⟩

/-- Restricting the public delta model is exactly a fixed-family mask. -/
theorem oldMask {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (X A B : Finset V) (w : V) (hBA : B ⊆ A) :
    deltaSetW G X B w = restrictPairs (deltaSetW G X A w) B := by
  ext e
  simp only [deltaSetW, edgeSetIn, restrictPairs, Finset.mem_filter,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨⟨hs, hc⟩, ha⟩, hn⟩
    refine ⟨⟨⟨⟨?_, hc⟩, ha⟩, hn⟩, ?_⟩
    · intro x hx
      obtain ⟨hxb, hxw⟩ := Finset.mem_filter.1 (hs hx)
      exact Finset.mem_filter.2 ⟨hBA hxb, hxw⟩
    · exact hs.trans (Finset.filter_subset _ _)
  · rintro ⟨⟨⟨⟨hs, hc⟩, ha⟩, hn⟩, hb⟩
    refine ⟨⟨⟨?_, hc⟩, ha⟩, hn⟩
    intro x hx
    exact Finset.mem_filter.2 ⟨hb hx, (Finset.mem_filter.1 (hs hx)).2⟩

/-- The correct all-pairs delta family has precisely two supported vertices per member. -/
theorem correctPairs {V : Type*}
    (G : SimpleGraph V) (X A : Finset V) (w : V) :
    ∀ e ∈ correctDelta G X A w, e ⊆ A ∧ e.card = 2 := by
  intro e he
  simp only [correctDelta, Finset.mem_filter, Finset.mem_powersetCard] at he
  exact ⟨he.1.1.trans (Finset.filter_subset _ _), he.1.2⟩

/-- Restricting the correct delta family keeps the same graph and common-neighbor exclusion. -/
theorem correctMask {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (X A B : Finset V) (w : V) (hBA : B ⊆ A) :
    correctDelta G X B w = restrictPairs (correctDelta G X A w) B := by
  ext e
  simp only [correctDelta, restrictPairs, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hs, hc⟩, hn⟩
    refine ⟨⟨⟨?_, hc⟩, hn⟩, ?_⟩
    · intro x hx
      obtain ⟨hxb, hxw⟩ := Finset.mem_filter.1 (hs hx)
      exact Finset.mem_filter.2 ⟨hBA hxb, hxw⟩
    · exact hs.trans (Finset.filter_subset _ _)
  · rintro ⟨⟨⟨hs, hc⟩, hn⟩, hb⟩
    refine ⟨⟨?_, hc⟩, hn⟩
    intro x hx
    exact Finset.mem_filter.2 ⟨hb hx, (Finset.mem_filter.1 (hs hx)).2⟩

/-- The old public Lemma 4.3 target holds for any distinct pair, without adjacency. -/
theorem lemma43NoEdge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X A : Finset V) (w v1 v2 : V) (r : ℕ)
    (hAcard : 3 < A.card) (hr : 3 < r) (hrA : r ≤ A.card)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hne : v1 ≠ v2) :
    ((r : ℝ) - 1) ^ 2 / (2 * (A.card : ℝ) ^ 2) ≤
      subsetProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((deltaSetW G X B w).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              (((deltaSetW G X A w).card : ℝ) / 3) + 16 * (r : ℝ)) := by
  let D := deltaSetW G X A w
  have hp := pair_containment_probability A v1 v2 hv1 hv2 hne r (by omega) hrA
  change ((r : ℝ) - 1) ^ 2 / (A.card : ℝ) ^ 2 ≤
    sampleProb A r (fun B => ({v1, v2} : Finset V) ⊆ B) at hp
  have hg := pairHalf A D v1 v2 r (oldPairs G X A w) hAcard hr hrA hv1 hv2 hne
  have heq : sampleProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((restrictPairs D B).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              ((D.card : ℝ) / 3) + 16 * (r : ℝ)) =
      subsetProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((deltaSetW G X B w).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              (((deltaSetW G X A w).card : ℝ) / 3) + 16 * (r : ℝ)) := by
    change sampleProb A r _ = sampleProb A r _
    apply sampleCongr
    intro B hB
    rw [oldMask G X A B w (Finset.mem_powersetCard.1 hB).1]
  rw [heq] at hg
  calc ((r : ℝ) - 1) ^ 2 / (2 * (A.card : ℝ) ^ 2) =
      (((r : ℝ) - 1) ^ 2 / (A.card : ℝ) ^ 2) / 2 := by ring
    _ ≤ sampleProb A r (fun B => ({v1, v2} : Finset V) ⊆ B) / 2 :=
      div_le_div_of_nonneg_right hp (by norm_num)
    _ ≤ _ := hg

/-- Lemma 4.3 uses all unordered pairs and the original graph in both neighborhood tests. -/
theorem lemma43Pairs {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X A : Finset V) (w v1 v2 : V) (r : ℕ)
    (hAcard : 3 < A.card) (hr : 3 < r) (hrA : r ≤ A.card)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hne : v1 ≠ v2) :
    ((r : ℝ) - 1) ^ 2 / (2 * (A.card : ℝ) ^ 2) ≤
      subsetProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((correctDelta G X B w).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              (((correctDelta G X A w).card : ℝ) / 3) + 16 * (r : ℝ)) := by
  let D := correctDelta G X A w
  have hp := pair_containment_probability A v1 v2 hv1 hv2 hne r (by omega) hrA
  change ((r : ℝ) - 1) ^ 2 / (A.card : ℝ) ^ 2 ≤
    sampleProb A r (fun B => ({v1, v2} : Finset V) ⊆ B) at hp
  have hg := pairHalf A D v1 v2 r (correctPairs G X A w) hAcard hr hrA hv1 hv2 hne
  have heq : sampleProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((restrictPairs D B).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              ((D.card : ℝ) / 3) + 16 * (r : ℝ)) =
      subsetProb A r (fun B =>
        ({v1, v2} : Finset V) ⊆ B ∧
          ((correctDelta G X B w).card : ℝ) ≤
            8 * ((r : ℝ) - 2) * ((r : ℝ) - 3) /
                (((A.card : ℝ) - 2) * ((A.card : ℝ) - 3)) *
              (((correctDelta G X A w).card : ℝ) / 3) + 16 * (r : ℝ)) := by
    change sampleProb A r _ = sampleProb A r _
    apply sampleCongr
    intro B hB
    rw [correctMask G X A B w (Finset.mem_powersetCard.1 hB).1]
  rw [heq] at hg
  calc ((r : ℝ) - 1) ^ 2 / (2 * (A.card : ℝ) ^ 2) =
      (((r : ℝ) - 1) ^ 2 / (A.card : ℝ) ^ 2) / 2 := by ring
    _ ≤ sampleProb A r (fun B => ({v1, v2} : Finset V) ⊆ B) / 2 :=
      div_le_div_of_nonneg_right hp (by norm_num)
    _ ≤ _ := hg

end Qatlib.Papers.TriangleFind14.SamplingCore
