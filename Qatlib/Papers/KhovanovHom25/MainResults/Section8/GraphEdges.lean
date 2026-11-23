/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathBridge

/-!
# Exact weighted edges for arbitrary multiplication graphs

Every edge comes from a transposition of an occupied and an unoccupied site.
The generating transposition reverses the edge and preserves particle number.
Thus the actual weighted graph is symmetric and its fixed sectors are closed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.GraphEdges

open Qatlib.Papers.KhovanovHom25.MainResults

/-- The actual occupied-site transposition generating one source edge. -/
def step {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ) : Vertex ℓ :=
  v.map (Equiv.swap i j).toEmbedding

/-- The source transposition is its own inverse. -/
theorem step_twice {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ) : step (step v i j) i j = v := by
  ext x
  simp only [step, Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_self]

/-- A particle-hole pair remains a particle-hole pair after its transposition. -/
theorem step_xor {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ) (h : (i ∈ v) ≠ (j ∈ v)) :
    (i ∈ step v i j) ≠ (j ∈ step v i j) := by
  simp only [step, Finset.mem_map_equiv, Equiv.symm_swap,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact h.symm

/-- One generator contributes to an edge exactly when it contributes to its reverse. -/
theorem generator_symm {ℓ : ℕ} (v w : Vertex ℓ) (i j : Fin ℓ) :
    ((i ∈ v) ≠ (j ∈ v) ∧ swapLabels v i j = w) ↔
      ((i ∈ w) ≠ (j ∈ w) ∧ swapLabels w i j = v) := by
  have reverse : ∀ v w : Vertex ℓ,
      ((i ∈ v) ≠ (j ∈ v) ∧ swapLabels v i j = w) →
        ((i ∈ w) ≠ (j ∈ w) ∧ swapLabels w i j = v) := by
    intro v w h
    obtain ⟨hxor, hw⟩ := h
    have hm : w = step v i j := by
      rw [← hw, swapLabels_map v i j hxor]
      rfl
    subst w
    rw [hm]
    have hx := step_xor v i j hxor
    refine ⟨hx, ?_⟩
    rw [swapLabels_map _ i j hx]
    exact step_twice v i j
  exact ⟨reverse v w, reverse w v⟩

/-- Actual source edge weights include all multiplicities and are symmetric. -/
theorem weight_symm {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (v w : Vertex ℓ) :
    edgeWeightAt p m v w = edgeWeightAt p m w v := by
  classical
  unfold edgeWeightAt
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact generator_symm v w (m a).1 (m a).2

/-- A nonstationary transposition cannot create a self-edge. -/
theorem step_ne {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ) (h : (i ∈ v) ≠ (j ∈ v)) :
    step v i j ≠ v := by
  intro heq
  have hm := congrArg (fun s : Vertex ℓ => i ∈ s) heq
  simp only [step, Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_left] at hm
  exact h hm.symm

/-- The source non-loop edge weight has zero diagonal, for every multiplication graph. -/
theorem weight_diag {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) (v : Vertex ℓ) :
    edgeWeightAt p m v v = 0 := by
  classical
  unfold edgeWeightAt
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro a _ ha
  apply step_ne v (m a).1 (m a).2 ha.1
  rw [swapLabels_map v (m a).1 (m a).2 ha.1] at ha
  exact ha.2

/-- Every actual source edge preserves the number of particles. -/
theorem weight_card {ℓ : ℕ} (p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    {v w : Vertex ℓ} (h : edgeWeightAt p m v w ≠ 0) : w.card = v.card := by
  classical
  unfold edgeWeightAt at h
  obtain ⟨a, ha⟩ := Finset.card_ne_zero.mp h
  obtain ⟨hxor, hw⟩ := (Finset.mem_filter.mp ha).2
  rw [swapLabels_map v (m a).1 (m a).2 hxor] at hw
  rw [← hw, Finset.card_map]

/-- A fixed particle sector has no edges to vertices outside that sector. -/
theorem weight_outside {ℓ : ℕ} (k p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    {v w : Vertex ℓ} (hv : v ∈ vertexSet ℓ k) (hw : w ∉ vertexSet ℓ k) :
    edgeWeightAt p m v w = 0 := by
  by_contra h
  apply hw
  rw [vertexSet, Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, (weight_card p m h).trans (Finset.mem_powersetCard.mp hv).2⟩

/-- The actual global degree sum equals its sum over the closed particle sector. -/
theorem degree_sector {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) {v : Vertex ℓ} (hv : v ∈ vertexSet ℓ k) :
    (weightedDegree p t m d v : ℝ) = 2 * (loopWeightAt p t m d v : ℝ) +
      ∑ w ∈ vertexSet ℓ k, (edgeWeightAt p m v w : ℝ) := by
  have hs : ∑ w ∈ (Finset.univ : Finset (Vertex ℓ)).erase v, (edgeWeightAt p m v w : ℝ) =
      ∑ w ∈ vertexSet ℓ k, (edgeWeightAt p m v w : ℝ) := by
    calc
      _ = ∑ w : Vertex ℓ, (edgeWeightAt p m v w : ℝ) := by
        simpa only [weight_diag, Nat.cast_zero, add_zero] using
          (Finset.sum_erase_add (s := Finset.univ)
            (f := fun w => (edgeWeightAt p m v w : ℝ)) (Finset.mem_univ v))
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ hw
        rw [weight_outside k p m hv hw, Nat.cast_zero]
  unfold weightedDegree
  push_cast
  rw [hs]

end Qatlib.Papers.KhovanovHom25.MainResults.GraphEdges
