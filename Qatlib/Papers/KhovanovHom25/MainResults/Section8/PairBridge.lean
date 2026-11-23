/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorPredicates
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairData
public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathEdges

/-!
# Ordered pair coordinates for the actual two-particle source sector

The map sends strictly ordered coordinates to their occupied-site subset.
It is injective and covers exactly the two-element source vertices. Set sizes,
loop weights and cuts can consequently be transferred without assuming any
isoperimetric conclusion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.KhovanovHom25.MainResults.PairBridge

open Qatlib.Papers.KhovanovHom25.MainResults

/-- The occupied-site subset associated with strictly ordered coordinates. -/
def vertex {N : ℕ} (p : PairFlow.Pair N) : Vertex (N + 1) := {p.val.1, p.val.2}

/-- Ordered coordinates always encode exactly two distinct particles. -/
theorem vertex_card {N : ℕ} (p : PairFlow.Pair N) : (vertex p).card = 2 := by
  rw [vertex, Finset.card_pair p.property.ne]

/-- Ordered pair coordinates determine their source subset uniquely. -/
theorem vertex_injective {N : ℕ} : Function.Injective (vertex (N := N)) := by
  intro p q heq
  have h1 : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
    have hp : p.val.1 ∈ vertex q := heq ▸ (by simp [vertex])
    simpa only [vertex, Finset.mem_insert, Finset.mem_singleton] using hp
  have h2 : q.val.1 = p.val.1 ∨ q.val.1 = p.val.2 := by
    have hq : q.val.1 ∈ vertex p := heq.symm ▸ (by simp [vertex])
    simpa only [vertex, Finset.mem_insert, Finset.mem_singleton] using hq
  have h3 : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
    have hp : p.val.2 ∈ vertex q := heq ▸ (by simp [vertex])
    simpa only [vertex, Finset.mem_insert, Finset.mem_singleton] using hp
  have h4 : q.val.2 = p.val.1 ∨ q.val.2 = p.val.2 := by
    have hq : q.val.2 ∈ vertex p := heq.symm ▸ (by simp [vertex])
    simpa only [vertex, Finset.mem_insert, Finset.mem_singleton] using hq
  have hp := PairFlow.coords p
  have hq := PairFlow.coords q
  apply PairFlow.pair_ext
  all_goals
    simp only [Fin.ext_iff] at h1 h2 h3 h4
    dsimp only [PairFlow.left, PairFlow.right] at hp hq ⊢
    omega

/-- Every source two-particle subset has strictly ordered pair coordinates. -/
theorem vertex_surjective {N : ℕ} (v : Vertex (N + 1))
    (hv : v ∈ vertexSet (N + 1) 2) : ∃ p : PairFlow.Pair N, vertex p = v := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hv).2
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨⟨(a, b), h⟩, rfl⟩
  · refine ⟨⟨(b, a), h⟩, ?_⟩
    exact Finset.pair_comm _ _

/-- Every ordered pair lies in the source sector. -/
theorem vertex_mem {N : ℕ} (p : PairFlow.Pair N) : vertex p ∈ vertexSet (N + 1) 2 := by
  rw [vertexSet, Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, vertex_card p⟩

/-- Pull back a set of actual source vertices along the occupied-site encoding. -/
def pull {N : ℕ} (S : Finset (Vertex (N + 1))) : Finset (PairFlow.Pair N) := by
  classical
  exact Finset.univ.filter (fun p => vertex p ∈ S)

/-- Membership in the coordinate pullback is exactly membership of the source vertex. -/
theorem mem_pull {N : ℕ} (S : Finset (Vertex (N + 1))) (p : PairFlow.Pair N) :
    p ∈ pull S ↔ vertex p ∈ S := by
  classical
  simp only [pull, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Pullback followed by the source encoding recovers every subset of the sector. -/
theorem image_pull {N : ℕ} (S : Finset (Vertex (N + 1)))
    (hS : S ⊆ vertexSet (N + 1) 2) : (pull S).image vertex = S := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_pull S p).mp hp
  · intro hv
    obtain ⟨p, rfl⟩ := vertex_surjective v (hS hv)
    exact Finset.mem_image.mpr ⟨p, (mem_pull S p).mpr hv, rfl⟩

/-- Source subsets and their actual coordinate pullbacks have equal cardinality. -/
theorem card_pull {N : ℕ} (S : Finset (Vertex (N + 1)))
    (hS : S ⊆ vertexSet (N + 1) 2) : (pull S).card = S.card := by
  classical
  calc
    _ = ((pull S).image vertex).card :=
      (Finset.card_image_of_injective (pull S) vertex_injective).symm
    _ = S.card := congrArg Finset.card (image_pull S hS)

/-- The source multiplication-loop indicator is exactly adjacency of the two particles. -/
theorem vertex_loop {N : ℕ} (p : PairFlow.Pair N) :
    loopWeightAt N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) (vertex p) =
      if PairFlow.IsLoop p then (1 / 2 : ℚ) else 0 := by
  classical
  have hc := PairFlow.coords p
  have ha : p.val.1.val < N := by
    unfold PairFlow.left PairFlow.right at hc
    omega
  let a : Fin N := ⟨p.val.1.val, ha⟩
  have hf : Finset.univ.filter (fun i : Fin N =>
      (twistedUnknotEdges N i).1 ∈ vertex p ∧
        (twistedUnknotEdges N i).2 ∈ vertex p) =
      if PairFlow.IsLoop p then {a} else ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, twistedUnknotEdges,
      vertex, Finset.mem_insert, Finset.mem_singleton]
    by_cases hg : PairFlow.IsLoop p
    · rw [ite_eq_left hg]
      simp only [Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      unfold PairFlow.IsLoop PairFlow.left PairFlow.right at hg
      unfold PairFlow.left PairFlow.right at hc
      dsimp only [a]
      omega
    · rw [ite_eq_right hg]
      simp only [Finset.notMem_empty, iff_false, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      unfold PairFlow.IsLoop PairFlow.left PairFlow.right at hg
      unfold PairFlow.left PairFlow.right at hc
      omega
  rw [loopWeightAt, hf]
  by_cases hg : PairFlow.IsLoop p <;> simp [hg]

/-- The actual source loop sum is one half the number of adjacent pair coordinates. -/
theorem loop_pull {N : ℕ} (S : Finset (Vertex (N + 1)))
    (hS : S ⊆ vertexSet (N + 1) 2) :
    loopSum N 0 (twistedUnknotEdges N) (fun i => Fin.elim0 i) S =
      (PairFlow.loopCount (pull S) : ℚ) / 2 := by
  classical
  conv_lhs =>
    rw [loopSum, ← image_pull S hS]
    rw [Finset.sum_image (fun a _ b _ h => vertex_injective h)]
  simp_rw [vertex_loop]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, PairFlow.loopCount]
  ring

/-- The adjacent transposition is an explicit arithmetic operation on site coordinates. -/
theorem swap_val {N : ℕ} (i : Fin N) (x : Fin (N + 1)) :
    ((Equiv.swap i.castSucc i.succ) x).val =
      if x.val = i.val then i.val + 1 else if x.val = i.val + 1 then i.val else x.val := by
  simp only [Equiv.swap_apply_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> rfl

/-- An explicitly computed transposition gives the corresponding source move. -/
theorem hop_of_swap {N : ℕ} (p q : PairFlow.Pair N) (i : Fin N)
    (hx : (i.castSucc ∈ vertex p) ≠ (i.succ ∈ vertex p))
    (ha : ((Equiv.swap i.castSucc i.succ) p.val.1).val = q.val.1.val)
    (hb : ((Equiv.swap i.castSucc i.succ) p.val.2).val = q.val.2.val) :
    PathModel.Hop (vertex p) (vertex q) := by
  refine ⟨i, hx, ?_⟩
  have ha' := Fin.ext ha
  have hb' := Fin.ext hb
  simp only [PathModel.flip, vertex, Finset.map_insert, Finset.map_singleton,
    Equiv.coe_toEmbedding, ha', hb']

/-- Raising the right coordinate executes the source transposition at that particle. -/
theorem hop_raise_right {N : ℕ} (p q : PairFlow.Pair N)
    (hl : PairFlow.left p = PairFlow.left q)
    (hr : PairFlow.right p + 1 = PairFlow.right q) :
    PathModel.Hop (vertex p) (vertex q) := by
  have hp := PairFlow.coords p
  have hq := PairFlow.coords q
  dsimp only [PairFlow.left, PairFlow.right] at hp hq hl hr
  let i : Fin N := ⟨p.val.2.val, by omega⟩
  apply hop_of_swap p q i
  · intro heq
    have hh := heq.to_iff
    simp only [vertex, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ] at hh
    dsimp only [i] at hh
    omega
  · rw [swap_val]
    dsimp only [i]
    split_ifs <;> omega
  · rw [swap_val]
    dsimp only [i]
    split_ifs <;> omega

/-- Raising the left coordinate executes its adjacent source transposition. -/
theorem hop_raise_left {N : ℕ} (p q : PairFlow.Pair N)
    (hr : PairFlow.right p = PairFlow.right q)
    (hl : PairFlow.left p + 1 = PairFlow.left q) :
    PathModel.Hop (vertex p) (vertex q) := by
  have hp := PairFlow.coords p
  have hq := PairFlow.coords q
  dsimp only [PairFlow.left, PairFlow.right] at hp hq hl hr
  let i : Fin N := ⟨p.val.1.val, by omega⟩
  apply hop_of_swap p q i
  · intro heq
    have hh := heq.to_iff
    simp only [vertex, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ] at hh
    dsimp only [i] at hh
    omega
  · rw [swap_val]
    dsimp only [i]
    split_ifs <;> omega
  · rw [swap_val]
    dsimp only [i]
    split_ifs <;> omega

/-- Every triangular coordinate edge is an actual adjacent source particle move. -/
theorem pair_hop {N : ℕ} (p q : PairFlow.Pair N) (h : PairFlow.Adj p q) :
    PathModel.Hop (vertex p) (vertex q) := by
  rcases h with ⟨hl, hr | hr⟩ | ⟨hr, hl | hl⟩
  · exact hop_raise_right p q hl hr
  · exact path_hop_symm (hop_raise_right q p hl.symm hr)
  · exact hop_raise_left p q hr hl
  · exact path_hop_symm (hop_raise_left q p hr.symm hl)

/-- Every coordinate cut edge injects into the actual weighted source cut. -/
theorem cut_pull_le {N : ℕ} (S : Finset (Vertex (N + 1)))
    (hS : S ⊆ vertexSet (N + 1) 2) :
    (PairFlow.cutCount (pull S) : ℚ) ≤ cutWeight N (twistedUnknotEdges N) S := by
  classical
  let weight := fun v w : Vertex (N + 1) =>
    (edgeWeightAt N (twistedUnknotEdges N) v w : ℚ)
  have hsingle : ∀ p : PairFlow.Pair N,
      ((Finset.univ.filter (fun q => q ∉ pull S ∧ PairFlow.Adj p q)).card : ℚ) ≤
        ∑ w ∈ (Finset.univ : Finset (Vertex (N + 1))) \ S, weight (vertex p) w := by
    intro p
    let T := Finset.univ.filter (fun q => q ∉ pull S ∧ PairFlow.Adj p q)
    have hsub : T.image vertex ⊆ (Finset.univ : Finset (Vertex (N + 1))) \ S := by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
      have hq' := (Finset.mem_filter.mp hq).2
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      exact hq'.1 ((mem_pull S q).mpr hmem)
    calc
      _ = ∑ _q ∈ T, (1 : ℚ) := by
        change (T.card : ℚ) = _
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ q ∈ T, weight (vertex p) (vertex q) := by
        apply Finset.sum_le_sum
        intro q hq
        have hhop := pair_hop p q (Finset.mem_filter.mp hq).2.2
        have hpos : 1 ≤ edgeWeightAt N (twistedUnknotEdges N) (vertex p) (vertex q) := by
          exact Nat.one_le_iff_ne_zero.mpr ((path_adj_iff N _ _).mpr hhop)
        change (1 : ℚ) ≤ (edgeWeightAt N (twistedUnknotEdges N) (vertex p) (vertex q) : ℚ)
        exact_mod_cast hpos
      _ = ∑ w ∈ T.image vertex, weight (vertex p) w :=
        (Finset.sum_image (fun a _ b _ h => vertex_injective h)).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro w _ _
        exact Nat.cast_nonneg _
  calc
    _ = ∑ p ∈ pull S,
        ((Finset.univ.filter (fun q => q ∉ pull S ∧ PairFlow.Adj p q)).card : ℚ) := by
      simp only [PairFlow.cutCount, Nat.cast_sum]
    _ ≤ ∑ p ∈ pull S,
        ∑ w ∈ (Finset.univ : Finset (Vertex (N + 1))) \ S, weight (vertex p) w :=
      Finset.sum_le_sum (fun p _ => hsingle p)
    _ = ∑ v ∈ (pull S).image vertex,
        ∑ w ∈ (Finset.univ : Finset (Vertex (N + 1))) \ S, weight v w :=
      (Finset.sum_image (f := fun v =>
        ∑ w ∈ (Finset.univ : Finset (Vertex (N + 1))) \ S, weight v w)
        (fun a _ b _ h => vertex_injective h)).symm
    _ = cutWeight N (twistedUnknotEdges N) S := by
      unfold cutWeight
      exact congrArg (fun U => ∑ v ∈ U,
        ∑ w ∈ (Finset.univ : Finset (Vertex (N + 1))) \ S, weight v w) (image_pull S hS)

end Qatlib.Papers.KhovanovHom25.MainResults.PairBridge
