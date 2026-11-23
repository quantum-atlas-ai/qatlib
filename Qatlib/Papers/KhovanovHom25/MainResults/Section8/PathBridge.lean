/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorPredicates
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathModel
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorKernel

/-!
# Exact weighted-graph bridge for twisted unknots

The generator-count edge weights equal actual adjacent particle-hole moves.
The signless matrix is restricted to the specified nonempty particle sector.
Its kernel vector is nonzero inside that sector, including the one-particle
sector, and cannot use an unrelated empty-sector coordinate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults

open Qatlib.Papers.KhovanovHom25.MainResults

/-- On unequal labels the source toggle formula is exactly the transposition action. -/
theorem swapLabels_map {ℓ : ℕ} (v : Vertex ℓ) (i j : Fin ℓ)
    (hxor : (i ∈ v) ≠ (j ∈ v)) :
    swapLabels v i j = v.map (Equiv.swap i j).toEmbedding := by
  ext x
  simp only [swapLabels, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hxi : x = i <;> by_cases hxj : x = j <;>
    by_cases hi : i ∈ v <;> by_cases hj : j ∈ v <;> simp_all [Equiv.swap_apply_def]

/-- A nonzero source edge weight is exactly an adjacent particle-hole move. -/
theorem path_adj_iff (N : ℕ) (v w : Vertex (N + 1)) :
    Adj N (twistedUnknotEdges N) v w ↔ PathModel.Hop v w := by
  classical
  unfold Adj edgeWeightAt
  rw [Finset.card_ne_zero]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hxor, hw⟩ := (Finset.mem_filter.mp hi).2
    simp only [twistedUnknotEdges] at hxor hw
    refine ⟨i, hxor, ?_⟩
    rw [swapLabels_map v i.castSucc i.succ hxor] at hw
    exact hw.symm
  · rintro ⟨i, hxor, hw⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change (i.castSucc ∈ v) ≠ (i.succ ∈ v) ∧ swapLabels v i.castSucc i.succ = w
    refine ⟨hxor, ?_⟩
    rw [swapLabels_map v i.castSucc i.succ hxor]
    exact hw.symm

/-- A source edge preserves the fixed particle number. -/
theorem path_edge_card (N : ℕ) {v w : Vertex (N + 1)}
    (h : edgeWeightAt N (twistedUnknotEdges N) v w ≠ 0) : w.card = v.card := by
  obtain ⟨i, _, rfl⟩ := (path_adj_iff N v w).mp h
  exact PathModel.flip_card v i

/-- The path graph has no non-loop self-edge. -/
theorem path_edge_diag (N : ℕ) (v : Vertex (N + 1)) :
    edgeWeightAt N (twistedUnknotEdges N) v v = 0 := by
  by_contra h
  exact PathModel.hop_color ((path_adj_iff N v v).mp h) rfl

/-- Every allowed particle sector is nonempty and connected by actual source edges. -/
theorem path_connected (N k : ℕ) (hk : k ≤ N + 1) :
    IsConnectedSector k N (twistedUnknotEdges N) := by
  refine ⟨?_, ?_⟩
  · simpa only [vertexSet, Finset.powersetCard_nonempty, Finset.card_univ,
      Fintype.card_fin] using hk
  · intro v hv w hw
    have hc : v.card = w.card :=
      (Finset.mem_powersetCard.mp hv).2.trans (Finset.mem_powersetCard.mp hw).2.symm
    exact Relation.ReflTransGen.mono (fun _ _ h => (path_adj_iff N _ _).mpr h)
      v w (PathModel.connected v w hc)

/-- No multiplication loop occurs in the zero- or one-particle sector. -/
theorem path_no_loops (N k : ℕ) (hk : k ≤ 1) (v : Vertex (N + 1))
    (hv : v ∈ vertexSet (N + 1) k) :
    loopWeightAt N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) v = 0 := by
  have hcard : v.card ≤ 1 := (Finset.mem_powersetCard.mp hv).2 ▸ hk
  have hempty : (Finset.univ.filter (fun a : Fin N =>
      (twistedUnknotEdges N a).1 ∈ v ∧ (twistedUnknotEdges N a).2 ∈ v)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _ ha
    have heq := Finset.card_le_one.mp hcard (twistedUnknotEdges N a).1 ha.1
      (twistedUnknotEdges N a).2 ha.2
    have hval := congrArg Fin.val heq
    simp only [twistedUnknotEdges, Fin.val_castSucc, Fin.val_succ] at hval
    omega
  simp only [loopWeightAt, hempty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_add]
  simp

/-- Edges from a fixed sector cannot leave that sector. -/
theorem path_edge_outside (N k : ℕ) {v w : Vertex (N + 1)}
    (hv : v ∈ vertexSet (N + 1) k) (hw : w ∉ vertexSet (N + 1) k) :
    edgeWeightAt N (twistedUnknotEdges N) v w = 0 := by
  by_contra h
  apply hw
  rw [vertexSet, Finset.mem_powersetCard]
  refine ⟨Finset.subset_univ _, ?_⟩
  rw [path_edge_card N h]
  exact (Finset.mem_powersetCard.mp hv).2

/-- The source matrix agrees exactly with the degree matrix on its fixed particle sector. -/
theorem path_sector_matrix (N k : ℕ) (hk : k ≤ 1) {v : Vertex (N + 1)}
    (hv : v ∈ vertexSet (N + 1) k) (u : Vertex (N + 1)) :
    signlessMatrix N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) v u =
      SectorKernel.matrix (vertexSet (N + 1) k)
        (fun a b => (edgeWeightAt N (twistedUnknotEdges N) a b : ℝ)) v u := by
  have hs : ∑ w ∈ (Finset.univ : Finset (Vertex (N + 1))).erase v,
      (edgeWeightAt N (twistedUnknotEdges N) v w : ℝ) =
      ∑ w ∈ vertexSet (N + 1) k, (edgeWeightAt N (twistedUnknotEdges N) v w : ℝ) := by
    calc
      _ = ∑ w : Vertex (N + 1), (edgeWeightAt N (twistedUnknotEdges N) v w : ℝ) := by
        simpa only [path_edge_diag, Nat.cast_zero, add_zero] using
          (Finset.sum_erase_add (s := Finset.univ)
            (f := fun w => (edgeWeightAt N (twistedUnknotEdges N) v w : ℝ))
            (Finset.mem_univ v))
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ hw
        rw [path_edge_outside N k hv hw, Nat.cast_zero]
  by_cases h : v = u
  · subst u
    simp only [signlessMatrix, signlessLap, SectorKernel.matrix]
    rw [weightedDegree, path_no_loops N k hk v hv]
    push_cast
    simpa only [mul_zero, zero_add] using hs
  · simp only [signlessMatrix, signlessLap, SectorKernel.matrix, ite_eq_right h]
    norm_cast

/-- The alternating vector lies in the kernel of the actual fixed-sector source matrix. -/
theorem path_sector_kernel (N k : ℕ) (hk : k ≤ 1) (hne : k ≤ N + 1) :
    HasSectorKernel k N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) := by
  classical
  refine ⟨SectorKernel.sign PathModel.color, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := (path_connected N k hne).1
    exact ⟨v, hv, SectorKernel.sign_ne_zero _ _⟩
  · intro v hv
    simp_rw [path_sector_matrix N k hk hv]
    apply SectorKernel.row_zero _ _ _ v hv
    · rw [path_edge_diag, Nat.cast_zero]
    · intro u _ hw
      apply PathModel.hop_color
      apply (path_adj_iff N v u).mp
      intro hz
      exact hw (by rw [hz, Nat.cast_zero])

end Qatlib.Papers.KhovanovHom25.MainResults
