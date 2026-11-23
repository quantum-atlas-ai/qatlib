/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathBridge

/-!
# Exact path-edge multiplicities

Distinct adjacent generators cannot give the same nonstationary particle move.
Consequently every nonzero edge has weight one and the source weights are
symmetric. These facts identify the source weighted cut with the ordinary cut
of ordered pairs in the two-particle sector.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.KhovanovHom25.MainResults

open Qatlib.Papers.KhovanovHom25.MainResults

open scoped Classical

/-- Repeating an adjacent exchange restores the original occupied subset. -/
theorem path_flip_twice {N : ℕ} (v : Vertex (N + 1)) (i : Fin N) :
    PathModel.flip (PathModel.flip v i) i = v := by
  ext x
  simp only [PathModel.flip, Finset.mem_map_equiv, Equiv.symm_swap,
    Equiv.swap_apply_self]

/-- The occupancy inequality is preserved by an adjacent exchange. -/
theorem path_flip_xor {N : ℕ} (v : Vertex (N + 1)) (i : Fin N)
    (h : (i.castSucc ∈ v) ≠ (i.succ ∈ v)) :
    (i.castSucc ∈ PathModel.flip v i) ≠ (i.succ ∈ PathModel.flip v i) := by
  simp only [PathModel.flip, Finset.mem_map_equiv, Equiv.symm_swap,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact h.symm

/-- Every actual particle-hole move can be reversed by its same generator. -/
theorem path_hop_symm {N : ℕ} {v w : Vertex (N + 1)} (h : PathModel.Hop v w) :
    PathModel.Hop w v := by
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, path_flip_xor v i hi, (path_flip_twice v i).symm⟩

/-- A nonstationary source edge has a unique adjacent generator. -/
theorem path_flip_inj {N : ℕ} (v : Vertex (N + 1)) {i j : Fin N}
    (hi : (i.castSucc ∈ v) ≠ (i.succ ∈ v))
    (hj : (j.castSucc ∈ v) ≠ (j.succ ∈ v))
    (heq : PathModel.flip v i = PathModel.flip v j) : i = j := by
  have hloc : ∀ {i j : Fin N},
      (i.castSucc ∈ v) ≠ (i.succ ∈ v) →
      PathModel.flip v i = PathModel.flip v j →
      i.castSucc = j.castSucc ∨ i.castSucc = j.succ := by
    intro i j hi heq
    by_contra h
    push Not at h
    have hm := congrArg (fun w : Vertex (N + 1) => i.castSucc ∈ w) heq
    simp only [PathModel.flip, Finset.mem_map_equiv, Equiv.symm_swap] at hm
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h.1 h.2] at hm
    exact hi hm.symm
  have h1 := hloc hi heq
  have h2 := hloc hj heq.symm
  apply Fin.ext
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h1 h2
  omega

/-- Each source path edge has multiplicity at most one. -/
theorem path_edge_le_one (N : ℕ) (v w : Vertex (N + 1)) :
    edgeWeightAt N (twistedUnknotEdges N) v w ≤ 1 := by
  classical
  unfold edgeWeightAt
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hixor, hiw⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨hjxor, hjw⟩ := (Finset.mem_filter.mp hj).2
  simp only [twistedUnknotEdges] at hixor hiw hjxor hjw
  apply path_flip_inj v hixor hjxor
  unfold PathModel.flip
  rw [← swapLabels_map v i.castSucc i.succ hixor,
    ← swapLabels_map v j.castSucc j.succ hjxor]
  exact hiw.trans hjw.symm

/-- A path edge weight is exactly the indicator of an actual move. -/
theorem path_edge_indicator (N : ℕ) (v w : Vertex (N + 1)) :
    edgeWeightAt N (twistedUnknotEdges N) v w =
      if PathModel.Hop v w then 1 else 0 := by
  classical
  have hn := path_edge_le_one N v w
  by_cases h : PathModel.Hop v w
  · rw [ite_eq_left h]
    have hp := (path_adj_iff N v w).mpr h
    unfold Adj at hp
    omega
  · rw [ite_eq_right h]
    by_contra hz
    exact h ((path_adj_iff N v w).mp hz)

/-- The exact path edge weights are symmetric under reversing an edge. -/
theorem path_edge_symm (N : ℕ) (v w : Vertex (N + 1)) :
    edgeWeightAt N (twistedUnknotEdges N) v w =
      edgeWeightAt N (twistedUnknotEdges N) w v := by
  classical
  rw [path_edge_indicator, path_edge_indicator]
  have h : PathModel.Hop v w ↔ PathModel.Hop w v := ⟨path_hop_symm, path_hop_symm⟩
  exact if_congr h rfl rfl

end Qatlib.Papers.KhovanovHom25.MainResults
