/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabNoLocMin14.MainResults.SourceMainResults
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
# Single-peaked positive eigenstates on the path

Jarret & Jordan, *Adiabatic optimization without local minima*, fixed arXiv:1405.7552v2,
§4.3 (p. 12), between Proposition 5 and Proposition 6. For a single-basin potential `W` on a
path graph and a strictly positive eigenstate `ψ` of `H_{G,W} = L_G + W`, the local maxima of
`ψ` form a connected set of vertices: `ψ` is single-peaked in the sense of §2 of the source.

The proof uses the discrete slope `s(i) = ψ(i) - ψ(i-1)` with the reflecting boundary
convention `ψ(-1) = ψ(0)` and `ψ(ℓ) = ψ(ℓ-1)`. The eigenvalue equation turns into
`s(i+1) - s(i) = (W(i) - E)ψ(i)`, so a vertex `x` is a local maximum exactly when
`s(x) ≥ 0 ≥ s(x+1)`. Single-basinedness of `W` then forces the set of such crossings to be
convex: a gap between two crossings would exhibit a strict peak of `W` between two points of a
strict sublevel set.

## Boundary

Only the path-graph bridge is proved. Positivity of the ground state (Perron--Frobenius),
eigenvalue ordering, the gap bounds of Propositions 4 and 6 and any adiabatic runtime claim
are outside this file.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabNoLocMin14.MainResults

open Qatlib.Papers.AdiabNoLocMin14.MainResults
open Qatlib.Concepts.GraphLaplacian.LaplacianPsd (degree_eq_mathlib)

/-! ## Path-graph reachability and convex vertex sets -/

/-- Consecutive vertices of the path graph are adjacent. -/
theorem pathGraph_adj_of_val_succ {n : ℕ} {u v : Fin n} (h : u.val + 1 = v.val) :
    (SimpleGraph.pathGraph n).Adj u v := by
  rw [SimpleGraph.pathGraph_adj]
  exact Or.inl h

/-- A walk in an induced path graph visits every index lying between its endpoints. -/
theorem pathGraph_walk_val_between {n : ℕ} {p : Fin n → Prop} {a b : {x : Fin n // p x}}
    (w : ((SimpleGraph.pathGraph n).induce {x | p x}).Walk a b) :
    ∀ t : ℕ, (a.1.val ≤ t ∧ t ≤ b.1.val) ∨ (b.1.val ≤ t ∧ t ≤ a.1.val) →
      ∃ x : {x : Fin n // p x}, x.1.val = t := by
  induction w with
  | nil =>
      rename_i u
      intro t ht
      have h1 : t = u.1.val := by rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      exact ⟨u, h1.symm⟩
  | cons h w ih =>
      rename_i u v z
      intro t ht
      have hval : u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val := by
        have hadj : (SimpleGraph.pathGraph n).Adj u.1 v.1 := SimpleGraph.induce_adj.mp h
        simpa [SimpleGraph.pathGraph_adj] using hadj
      by_cases hcase : (v.1.val ≤ t ∧ t ≤ z.1.val) ∨ (z.1.val ≤ t ∧ t ≤ v.1.val)
      · exact ih t hcase
      · have hn1 : ¬ (v.1.val ≤ t ∧ t ≤ z.1.val) := fun hh => hcase (Or.inl hh)
        have hn2 : ¬ (z.1.val ≤ t ∧ t ≤ v.1.val) := fun hh => hcase (Or.inr hh)
        have htu : t = u.1.val := by
          rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hval with hv | hv <;> omega
        exact ⟨u, htu.symm⟩

/-- A vertex set containing every vertex between any two of its members is connected in the
induced path graph. -/
theorem reachable_induce_of_convex {n : ℕ} {A : Set (Fin n)}
    (hconv : ∀ x y z : Fin n, x ≤ y → y ≤ z → x ∈ A → z ∈ A → y ∈ A) {u v : A}
    (hle : u.1 ≤ v.1) : ((SimpleGraph.pathGraph n).induce A).Reachable u v := by
  have hle' : u.1.val ≤ v.1.val := Fin.le_iff_val_le_val.mp hle
  have key : ∀ k : ℕ, ∀ u v : A, u.1.val ≤ v.1.val → v.1.val = u.1.val + k →
      ((SimpleGraph.pathGraph n).induce A).Reachable u v := by
    intro k
    induction k with
    | zero =>
        intro u v hle hk
        have huv : u = v := by
          apply Subtype.ext
          apply Fin.ext
          omega
        exact huv ▸ SimpleGraph.Reachable.rfl
    | succ k ih =>
        intro u v hle hk
        have hstep : u.1.val + 1 ≤ v.1.val := by
          rw [hk]
          exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) u.1.val
        have hlt : u.1.val + 1 < n := Nat.lt_of_le_of_lt hstep v.1.isLt
        have hmem : (⟨u.1.val + 1, hlt⟩ : Fin n) ∈ A :=
          hconv u.1 ⟨u.1.val + 1, hlt⟩ v.1
            (Fin.le_iff_val_le_val.mpr (Nat.le_succ u.1.val))
            (Fin.le_iff_val_le_val.mpr hstep) u.2 v.2
        let w : A := ⟨⟨u.1.val + 1, hlt⟩, hmem⟩
        have hw : w.1.val = u.1.val + 1 := rfl
        have hadj : ((SimpleGraph.pathGraph n).induce A).Adj u w := by
          rw [SimpleGraph.induce_adj]
          exact pathGraph_adj_of_val_succ (by rw [hw])
        refine (SimpleGraph.Adj.reachable hadj).trans (ih w v ?_ ?_)
        · rw [hw]
          exact hstep
        · rw [hk, hw]
          omega
  exact key (v.1.val - u.1.val) u v hle' (Nat.add_sub_of_le hle').symm

/-- On a path graph, a connected induced vertex set contains every index between any two of its
members. -/
theorem convex_of_levelSet_preconnected {n : ℕ} {W : Fin n → ℝ} (c : ℝ)
    (hpre : ((SimpleGraph.pathGraph n).induce {x : Fin n | W x < c}).Preconnected)
    {i j k : Fin n} (hij : i ≤ j) (hjk : j ≤ k) (hi : W i < c) (hk : W k < c) : W j < c := by
  obtain ⟨w⟩ := hpre ⟨i, hi⟩ ⟨k, hk⟩
  obtain ⟨x, hx⟩ := pathGraph_walk_val_between w j.val
    (Or.inl ⟨Fin.le_iff_val_le_val.mp hij, Fin.le_iff_val_le_val.mp hjk⟩)
  have hxj : x.1 = j := Fin.ext hx
  simpa [hxj] using x.2

/-- A strict sublevel set of a single-basin potential on a path is an interval of indices. -/
theorem exists_interval_of_levelSet {n : ℕ} {W : Fin n → ℝ} {c : ℝ}
    (hconv : ∀ (d : ℝ) (i j k : Fin n), i ≤ j → j ≤ k → W i < d → W k < d → W j < d)
    (hne : ∃ w : Fin n, W w < c) :
    ∃ A B : ℕ, A < n ∧ B < n ∧ ∀ x : Fin n, W x < c ↔ A ≤ x.val ∧ x.val ≤ B := by
  classical
  let F : Finset (Fin n) := Finset.univ.filter (fun x => W x < c)
  have hF : F.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, by simp [F, hw]⟩
  refine ⟨(F.min' hF).val, (F.max' hF).val, (F.min' hF).isLt, (F.max' hF).isLt, fun x => ?_⟩
  constructor
  · intro hx
    have hxF : x ∈ F := by simp [F, hx]
    have h1 : F.min' hF ≤ x := F.min'_le x hxF
    have h2 : x ≤ F.max' hF := F.le_max' x hxF
    exact ⟨Fin.le_iff_val_le_val.mp h1, Fin.le_iff_val_le_val.mp h2⟩
  · rintro ⟨h1, h2⟩
    have hamin : W (F.min' hF) < c := by
      have := F.min'_mem hF
      simpa [F] using this
    have hbmax : W (F.max' hF) < c := by
      have := F.max'_mem hF
      simpa [F] using this
    exact hconv c (F.min' hF) x (F.max' hF) (Fin.le_iff_val_le_val.mpr h1)
      (Fin.le_iff_val_le_val.mpr h2) hamin hbmax

/-! ## The slope sequence and the path Laplacian -/

/-- The reflection extension of a vertex function to all natural numbers: past the last vertex the
value of the last vertex is repeated, so the path boundary behaves as a reflecting wall. -/
def reflExt {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : ℕ) : ℝ :=
  if h : i < ℓ then ψ ⟨i, h⟩ else if h0 : 0 < ℓ then ψ ⟨ℓ - 1, by omega⟩ else 0

/-- Inside the path, the reflection extension is the original function. -/
theorem reflExt_of_lt {ℓ : ℕ} {ψ : Fin ℓ → ℝ} {i : ℕ} (h : i < ℓ) :
    reflExt ψ i = ψ ⟨i, h⟩ := by
  simp [reflExt, h]

/-- Beyond the last vertex, the reflection extension repeats the last value. -/
theorem reflExt_of_le {ℓ : ℕ} {ψ : Fin ℓ → ℝ} {i : ℕ} (h0 : 0 < ℓ) (h : ℓ ≤ i) :
    reflExt ψ i = ψ ⟨ℓ - 1, by omega⟩ := by
  simp [reflExt, Nat.not_lt.mpr h, h0]

/-- The discrete slope `s(i) = ψ(i) - ψ(i-1)`, with the reflecting convention at `i = 0`. -/
def slope {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : ℕ) : ℝ := reflExt ψ i - reflExt ψ (i - 1)

/-- The slope vanishes at the reflecting wall on the left. -/
theorem slope_zero {ℓ : ℕ} (ψ : Fin ℓ → ℝ) : slope ψ 0 = 0 := by
  simp [slope]

/-- The slope vanishes at the reflecting wall on the right. -/
theorem slope_last {ℓ : ℕ} {ψ : Fin ℓ → ℝ} (h0 : 0 < ℓ) : slope ψ ℓ = 0 := by
  have h1 : ℓ - 1 < ℓ := by omega
  simp [slope, reflExt, h0, h1]

/-- The slope difference is the second difference of the reflected extension. -/
theorem slope_succ_sub {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : ℕ) :
    slope ψ (i + 1) - slope ψ i =
      reflExt ψ (i + 1) - 2 * reflExt ψ i + reflExt ψ (i - 1) := by
  unfold slope
  have h1 : i + 1 - 1 = i := by omega
  rw [h1]
  ring

/-- Inside the path, the slope is the difference of two consecutive vertex values. -/
theorem slope_eq_sub {ℓ : ℕ} {ψ : Fin ℓ → ℝ} {i : ℕ} (h1 : 0 < i) (h2 : i < ℓ) :
    slope ψ i = ψ ⟨i, h2⟩ - ψ ⟨i - 1, by omega⟩ := by
  unfold slope
  rw [reflExt_of_lt h2, reflExt_of_lt (by omega : i - 1 < ℓ)]

/-! ## Vertex sums and degrees on the path -/

/-- The predecessor indicator sums to the value at the predecessor of a non-first vertex. -/
theorem sum_ite_pred {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (i : Fin ℓ) (g : Fin ℓ → M)
    (h : 0 < i.val) :
    ∑ y : Fin ℓ, (if y.val + 1 = i.val then g y else (0 : M)) = g ⟨i.val - 1, by omega⟩ := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun y : Fin ℓ => y.val + 1 = i.val) =
      {(⟨i.val - 1, by omega⟩ : Fin ℓ)} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hy
      refine Fin.ext ?_
      dsimp only [Fin.val_mk]
      omega
    · intro hy
      rw [hy]
      dsimp only [Fin.val_mk]
      exact Nat.sub_add_cancel h
  rw [hset, Finset.sum_singleton]

/-- The predecessor indicator vanishes at the first vertex. -/
theorem sum_ite_pred_zero {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (i : Fin ℓ) (g : Fin ℓ → M)
    (h : i.val = 0) :
    ∑ y : Fin ℓ, (if y.val + 1 = i.val then g y else (0 : M)) = 0 := by
  refine Finset.sum_eq_zero fun y _ => ?_
  have hy : ¬ (y.val + 1 = i.val) := by omega
  simp [hy]

/-- The successor indicator sums to the value at the successor of a non-last vertex. -/
theorem sum_ite_succ {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (i : Fin ℓ) (g : Fin ℓ → M)
    (h : i.val + 1 < ℓ) :
    ∑ y : Fin ℓ, (if i.val + 1 = y.val then g y else (0 : M)) = g ⟨i.val + 1, h⟩ := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun y : Fin ℓ => i.val + 1 = y.val) =
      {(⟨i.val + 1, h⟩ : Fin ℓ)} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hy
      refine Fin.ext ?_
      dsimp only [Fin.val_mk]
      omega
    · intro hy
      rw [hy]
  rw [hset, Finset.sum_singleton]

/-- The successor indicator vanishes at the last vertex. -/
theorem sum_ite_succ_zero {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (i : Fin ℓ) (g : Fin ℓ → M)
    (h : i.val + 1 = ℓ) :
    ∑ y : Fin ℓ, (if i.val + 1 = y.val then g y else (0 : M)) = 0 := by
  refine Finset.sum_eq_zero fun y _ => ?_
  have hy : ¬ (i.val + 1 = y.val) := by omega
  simp [hy]

/-- The neighbours of a path vertex are given by the predecessor and successor indicators. -/
theorem sum_neighborFinset_split {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : Fin ℓ) :
    ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y =
      (∑ y : Fin ℓ, (if y.val + 1 = i.val then ψ y else 0)) +
        (∑ y : Fin ℓ, (if i.val + 1 = y.val then ψ y else 0)) := by
  have hset : (SimpleGraph.pathGraph ℓ).neighborFinset i =
      Finset.univ.filter (fun y : Fin ℓ => y.val + 1 = i.val ∨ i.val + 1 = y.val) := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, or_comm]
  rw [hset, Finset.sum_filter]
  have hsplit : ∀ y : Fin ℓ,
      (if y.val + 1 = i.val ∨ i.val + 1 = y.val then ψ y else 0) =
        (if y.val + 1 = i.val then ψ y else 0) + (if i.val + 1 = y.val then ψ y else 0) := by
    intro y
    by_cases h1 : y.val + 1 = i.val
    · have h2 : ¬ (i.val + 1 = y.val) := by omega
      simp [h1, h2]
    · by_cases h2 : i.val + 1 = y.val
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib]

/-- The neighbour sum at the first vertex. -/
theorem sum_neighborFinset_of_zero {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : Fin ℓ) (hi : i.val = 0)
    (h1 : 1 < ℓ) :
    ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y = ψ ⟨1, h1⟩ := by
  have hlt : i.val + 1 < ℓ := by omega
  rw [sum_neighborFinset_split, sum_ite_pred_zero i ψ hi, sum_ite_succ i ψ hlt, zero_add]
  have h2 : (⟨i.val + 1, hlt⟩ : Fin ℓ) = ⟨1, h1⟩ := by
    refine Fin.ext ?_
    dsimp only [Fin.val_mk]
    omega
  rw [h2]

/-- The neighbour sum at an interior vertex. -/
theorem sum_neighborFinset_of_interior {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : Fin ℓ) (h0 : 0 < i.val)
    (h1 : i.val + 1 < ℓ) :
    ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y =
      ψ ⟨i.val - 1, by omega⟩ + ψ ⟨i.val + 1, h1⟩ := by
  rw [sum_neighborFinset_split, sum_ite_pred i ψ h0, sum_ite_succ i ψ h1]

/-- The neighbour sum at the last vertex. -/
theorem sum_neighborFinset_of_last {ℓ : ℕ} (ψ : Fin ℓ → ℝ) (i : Fin ℓ) (h0 : 0 < i.val)
    (h1 : i.val + 1 = ℓ) :
    ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y = ψ ⟨i.val - 1, by omega⟩ := by
  rw [sum_neighborFinset_split, sum_ite_pred i ψ h0, sum_ite_succ_zero i ψ h1, add_zero]

/-- The degree of the first vertex. -/
theorem degree_of_zero {ℓ : ℕ} (i : Fin ℓ) (hi : i.val = 0) (h1 : 1 < ℓ) :
    ((SimpleGraph.pathGraph ℓ).degree i : ℝ) = 1 := by
  have hset : (SimpleGraph.pathGraph ℓ).neighborFinset i = {⟨1, h1⟩} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · refine Fin.ext ?_
        dsimp only [Fin.val_mk]
        omega
      · refine Fin.ext ?_
        dsimp only [Fin.val_mk]
        omega
    · rintro rfl
      left
      dsimp only [Fin.val_mk]
      omega
  have hcard : (SimpleGraph.pathGraph ℓ).degree i = 1 := by
    simp [SimpleGraph.degree, hset]
  rw [hcard]
  norm_num

/-- The degree of an interior vertex. -/
theorem degree_of_interior {ℓ : ℕ} (i : Fin ℓ) (h0 : 0 < i.val) (h1 : i.val + 1 < ℓ) :
    ((SimpleGraph.pathGraph ℓ).degree i : ℝ) = 2 := by
  have hset : (SimpleGraph.pathGraph ℓ).neighborFinset i =
      {⟨i.val - 1, by omega⟩, ⟨i.val + 1, h1⟩} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · right
        refine Fin.ext ?_
        dsimp only [Fin.val_mk]
        omega
      · left
        refine Fin.ext ?_
        dsimp only [Fin.val_mk]
        omega
    · rintro (rfl | rfl)
      · right
        dsimp only [Fin.val_mk]
        exact Nat.sub_add_cancel h0
      · left
        dsimp only [Fin.val_mk]
  have hcard : (SimpleGraph.pathGraph ℓ).degree i = 2 := by
    simp only [SimpleGraph.degree, hset]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      intro hc
      have hcv := congrArg Fin.val hc
      dsimp only [Fin.val_mk] at hcv
      omega)]
    simp
  rw [hcard]
  norm_num

/-- The degree of the last vertex. -/
theorem degree_of_last {ℓ : ℕ} (i : Fin ℓ) (h0 : 0 < i.val) (h1 : i.val + 1 = ℓ) :
    ((SimpleGraph.pathGraph ℓ).degree i : ℝ) = 1 := by
  have hset : (SimpleGraph.pathGraph ℓ).neighborFinset i = {⟨i.val - 1, by omega⟩} := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · refine Fin.ext ?_
        dsimp only [Fin.val_mk]
        omega
      · refine Fin.ext ?_
        dsimp only [Fin.val_mk]
        omega
    · rintro rfl
      right
      dsimp only [Fin.val_mk]
      exact Nat.sub_add_cancel h0
  have hcard : (SimpleGraph.pathGraph ℓ).degree i = 1 := by
    simp [SimpleGraph.degree, hset]
  rw [hcard]
  norm_num

/-- The path Laplacian of a vertex equals the second difference of the reflected extension; this
is the vertex form of source eq. (23) for `SimpleGraph.pathGraph`. -/
theorem deltaSq_pathGraph {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (ψ : Fin ℓ → ℝ) (i : Fin ℓ) :
    deltaSq (SimpleGraph.pathGraph ℓ) ψ i =
      reflExt ψ (i.val + 1) - 2 * reflExt ψ i.val + reflExt ψ (i.val - 1) := by
  rw [deltaSq, degree_eq_mathlib]
  have hi : ψ i = reflExt ψ i.val := (reflExt_of_lt i.isLt).symm
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1ℓ : (1 : ℕ) < ℓ := by omega
    let v1 : Fin ℓ := ⟨1, h1ℓ⟩
    have hdeg : ((SimpleGraph.pathGraph ℓ).degree i : ℝ) = 1 := degree_of_zero i h0 h1ℓ
    have hsum : ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y = ψ v1 :=
      sum_neighborFinset_of_zero ψ i h0 h1ℓ
    have hs1 : ψ v1 = reflExt ψ 1 := (reflExt_of_lt h1ℓ).symm
    rw [hdeg, hsum, hs1, hi, h0]
    simp only [Nat.zero_add, Nat.zero_sub]
    ring
  · by_cases hlast : i.val + 1 = ℓ
    · let vp : Fin ℓ := ⟨i.val - 1, by omega⟩
      have hdeg : ((SimpleGraph.pathGraph ℓ).degree i : ℝ) = 1 := degree_of_last i hpos hlast
      have hsum : ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y = ψ vp :=
        sum_neighborFinset_of_last ψ i hpos hlast
      have hpred : ψ vp = reflExt ψ (i.val - 1) :=
        (reflExt_of_lt (by omega : i.val - 1 < ℓ)).symm
      have hnext : reflExt ψ (i.val + 1) = ψ i := by
        have h1 : reflExt ψ (i.val + 1) = ψ ⟨ℓ - 1, by omega⟩ :=
          reflExt_of_le (by omega : 0 < ℓ) (by omega : ℓ ≤ i.val + 1)
        have h2 : (⟨ℓ - 1, by omega⟩ : Fin ℓ) = i := by
          refine Fin.ext ?_
          dsimp only [Fin.val_mk]
          omega
        rw [h1, h2]
      rw [hdeg, hsum, hpred, hnext, hi]
      ring
    · have hlt : i.val + 1 < ℓ := by omega
      let vp : Fin ℓ := ⟨i.val - 1, by omega⟩
      let vs : Fin ℓ := ⟨i.val + 1, hlt⟩
      have hdeg : ((SimpleGraph.pathGraph ℓ).degree i : ℝ) = 2 := degree_of_interior i hpos hlt
      have hsum : ∑ y ∈ (SimpleGraph.pathGraph ℓ).neighborFinset i, ψ y = ψ vp + ψ vs :=
        sum_neighborFinset_of_interior ψ i hpos hlt
      have hpred : ψ vp = reflExt ψ (i.val - 1) :=
        (reflExt_of_lt (by omega : i.val - 1 < ℓ)).symm
      have hsucc : ψ vs = reflExt ψ (i.val + 1) := (reflExt_of_lt hlt).symm
      rw [hdeg, hsum, hpred, hsucc, hi]
      ring

/-! ## Local maxima as crossings of the slope -/

/-- A vertex of the path is a local maximum exactly when the slope changes sign there: the slope
arrives nonnegative and leaves nonpositive. -/
theorem isLocalMax_iff_slope {ℓ : ℕ} {ψ : Fin ℓ → ℝ} (h0 : 0 < ℓ) (x : Fin ℓ) :
    IsLocalMax (SimpleGraph.pathGraph ℓ) ψ x ↔ 0 ≤ slope ψ x.val ∧ slope ψ (x.val + 1) ≤ 0 := by
  constructor
  · intro hmax
    have hleft : 0 ≤ slope ψ x.val := by
      rcases Nat.eq_zero_or_pos x.val with hx | hx
      · rw [hx, slope_zero]
      · have hsub : slope ψ x.val = ψ x - ψ ⟨x.val - 1, by omega⟩ := by
          rw [slope_eq_sub (ψ := ψ) hx x.isLt]
        have hadj : (SimpleGraph.pathGraph ℓ).Adj x ⟨x.val - 1, by omega⟩ := by
          rw [SimpleGraph.pathGraph_adj]
          refine Or.inr ?_
          dsimp only [Fin.val_mk]
          exact Nat.sub_add_cancel hx
        have hle := hmax _ hadj
        linarith
    have hright : slope ψ (x.val + 1) ≤ 0 := by
      by_cases hlast : x.val + 1 = ℓ
      · rw [hlast, slope_last h0]
      · have hlt : x.val + 1 < ℓ := by omega
        have hsub : slope ψ (x.val + 1) = ψ ⟨x.val + 1, hlt⟩ - ψ x := by
          rw [slope_eq_sub (ψ := ψ) (by omega : 0 < x.val + 1) hlt]
          congr 2
        have hadj : (SimpleGraph.pathGraph ℓ).Adj x ⟨x.val + 1, hlt⟩ :=
          pathGraph_adj_of_val_succ rfl
        have hle := hmax _ hadj
        linarith
    exact ⟨hleft, hright⟩
  · rintro ⟨h1, h2⟩ y hy
    have hval : y.val + 1 = x.val ∨ x.val + 1 = y.val := by
      have h := hy
      rw [SimpleGraph.pathGraph_adj] at h
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hval with hv | hv
    · have hx : 0 < x.val := by omega
      have hy2 : y.val = x.val - 1 := by omega
      have hsub : slope ψ x.val = ψ x - ψ y := by
        rw [slope_eq_sub (ψ := ψ) hx x.isLt]
        congr 2
        exact (Fin.ext hy2).symm
      linarith
    · have hlt : x.val + 1 < ℓ := by omega
      have hy2 : y.val = x.val + 1 := by omega
      have hsub : slope ψ (x.val + 1) = ψ y - ψ x := by
        rw [slope_eq_sub (ψ := ψ) (by omega : 0 < x.val + 1) hlt]
        congr 2
        exact (Fin.ext hy2).symm
      linarith

/-! ## Proposition 5 implies single-peakedness on the path -/

/-- **Proposition 5 on the path**, source §4.3 p. 12, between Proposition 5 and Proposition 6.
A strictly positive eigenstate of `H_{G,W} = L_G + W` on a path graph with single-basin
potential `W` is single-peaked. -/
theorem prop5_path_isSinglePeaked {ℓ : ℕ} (W ψ : Fin ℓ → ℝ) {E : ℝ}
    (h : IsEigenstate (SimpleGraph.pathGraph ℓ) W ψ E) (hpos : ∀ x, 0 < ψ x)
    (hsingle : IsSingleBasin (SimpleGraph.pathGraph ℓ) W) :
    IsSinglePeaked (SimpleGraph.pathGraph ℓ) ψ := by
  classical
  rcases Nat.lt_or_ge ℓ 2 with hsmall | hℓ
  · have : Subsingleton (Fin ℓ) := by
      refine ⟨fun a b => Fin.ext ?_⟩
      have ha := a.isLt
      have hb := b.isLt
      omega
    show ((SimpleGraph.pathGraph ℓ).induce
      {x : Fin ℓ | IsLocalMax (SimpleGraph.pathGraph ℓ) ψ x}).Preconnected
    intro u v
    have huv : u = v := Subtype.ext (Subsingleton.elim u.1 v.1)
    exact huv ▸ SimpleGraph.Reachable.rfl
  · have h0 : 0 < ℓ := by omega
    have hrec : ∀ i : Fin ℓ, slope ψ (i.val + 1) - slope ψ i.val = (W i - E) * ψ i := by
      intro i
      rw [slope_succ_sub, ← deltaSq_pathGraph hℓ ψ i]
      exact deltaSq_eq_mul_sub (G := SimpleGraph.pathGraph ℓ) h i
    have hrecN : ∀ (i : ℕ) (hi : i < ℓ),
        slope ψ (i + 1) - slope ψ i = (W ⟨i, hi⟩ - E) * ψ ⟨i, hi⟩ := by
      intro i hi
      simpa using hrec ⟨i, hi⟩
    let Wn : ℕ → ℝ := fun i => if h : i < ℓ then W ⟨i, h⟩ else 0
    have hWn : ∀ (i : ℕ) (h : i < ℓ), Wn i = W ⟨i, h⟩ := by
      intro i h
      simp [Wn, h]
    have hstep_up : ∀ (i : ℕ), i < ℓ → E < Wn i → slope ψ i < slope ψ (i + 1) := by
      intro i hi hWi
      have hr := hrecN i hi
      have hp := hpos ⟨i, hi⟩
      have hWi' : E < W ⟨i, hi⟩ := by rw [← hWn i hi]; exact hWi
      nlinarith [hr, hp]
    have hstep_down : ∀ (i : ℕ), i < ℓ → Wn i < E → slope ψ (i + 1) < slope ψ i := by
      intro i hi hWi
      have hr := hrecN i hi
      have hp := hpos ⟨i, hi⟩
      have hWi' : W ⟨i, hi⟩ < E := by rw [← hWn i hi]; exact hWi
      nlinarith [hr, hp]
    have mono_le : ∀ {f : ℕ → ℝ} {lo hi : ℕ}, (∀ k, lo ≤ k → k < hi → f k ≤ f (k + 1)) →
        ∀ i j, lo ≤ i → i ≤ j → j ≤ hi → f i ≤ f j := by
      intro f lo hi hf i j _ hij hj
      have key : ∀ d : ℕ, i + d ≤ hi → f i ≤ f (i + d) := by
        intro d
        induction d with
        | zero => intro _; simp
        | succ d ihd =>
            intro hd
            have h1 : f i ≤ f (i + d) := ihd (by omega)
            have h2 : f (i + d) ≤ f (i + d + 1) := hf (i + d) (by omega) (by omega)
            calc f i ≤ f (i + d) := h1
              _ ≤ f (i + d + 1) := h2
              _ = f (i + (d + 1)) := by rw [Nat.add_assoc]
      have := key (j - i) (by omega)
      rwa [Nat.add_sub_cancel' hij] at this
    have mono_ge : ∀ {f : ℕ → ℝ} {lo hi : ℕ}, (∀ k, lo ≤ k → k < hi → f (k + 1) ≤ f k) →
        ∀ i j, lo ≤ i → i ≤ j → j ≤ hi → f j ≤ f i := by
      intro f lo hi hf i j _ hij hj
      have key : ∀ d : ℕ, i + d ≤ hi → f (i + d) ≤ f i := by
        intro d
        induction d with
        | zero => intro _; simp
        | succ d ihd =>
            intro hd
            have h1 : f (i + d + 1) ≤ f (i + d) := hf (i + d) (by omega) (by omega)
            have h2 : f (i + d) ≤ f i := ihd (by omega)
            calc f (i + (d + 1)) = f (i + d + 1) := by rw [Nat.add_assoc]
              _ ≤ f (i + d) := h1
              _ ≤ f i := h2
      have := key (j - i) (by omega)
      rwa [Nat.add_sub_cancel' hij] at this
    have hqc : ∀ (i j k : ℕ) (hi : i < ℓ) (hj : j < ℓ) (hk : k < ℓ), i < j → j < k →
        Wn j ≤ max (Wn i) (Wn k) := by
      intro i j k hi hj hk hij hjk
      by_contra hcon
      push Not at hcon
      rw [hWn i hi, hWn k hk, hWn j hj] at hcon
      have h1 : W ⟨i, hi⟩ < W ⟨j, hj⟩ := lt_of_le_of_lt (le_max_left _ _) hcon
      have h2 : W ⟨k, hk⟩ < W ⟨j, hj⟩ := lt_of_le_of_lt (le_max_right _ _) hcon
      exact absurd
        (convex_of_levelSet_preconnected (W := W) (c := W ⟨j, hj⟩)
          (hsingle (W ⟨j, hj⟩)) (le_of_lt hij) (le_of_lt hjk) h1 h2) (lt_irrefl _)
    have hcross := isLocalMax_iff_slope (ψ := ψ) h0
    have hconv_cross : ∀ x y z : Fin ℓ, x ≤ y → y ≤ z → 0 ≤ slope ψ x.val →
        slope ψ (x.val + 1) ≤ 0 → 0 ≤ slope ψ z.val → slope ψ (z.val + 1) ≤ 0 →
        0 ≤ slope ψ y.val ∧ slope ψ (y.val + 1) ≤ 0 := by
      intro x y z hxy hyz hx1 hx2 hz1 hz2
      by_cases hne : ∃ w : Fin ℓ, W w < E
      · obtain ⟨A, B, hAℓ, hBℓ, hAB⟩ := exists_interval_of_levelSet
          (W := W) (c := E) (fun d i j k hij hjk hi hk =>
            convex_of_levelSet_preconnected d (hsingle d) hij hjk hi hk) hne
        have hleft : ∀ (i : ℕ) (hi : i < ℓ), i < A → slope ψ i ≤ slope ψ (i + 1) := by
          intro i hi hiA
          by_cases hlt : W ⟨i, hi⟩ < E
          · exact absurd (by simpa using ((hAB ⟨i, hi⟩).mp hlt).1) (by omega)
          · push Not at hlt
            rcases lt_or_eq_of_le hlt with hgt | heq
            · exact le_of_lt (hstep_up i hi (by rw [hWn i hi]; exact hgt))
            · have hstep_flat : slope ψ i = slope ψ (i + 1) := by
                have hr := hrecN i hi
                rw [heq] at hr
                have hz : slope ψ (i + 1) - slope ψ i = 0 := by simpa using hr
                linarith
              exact le_of_eq hstep_flat
        have hmid : ∀ (i : ℕ) (hi : i < ℓ), A ≤ i → i ≤ B → slope ψ (i + 1) ≤ slope ψ i := by
          intro i hi hiA hiB
          have hlt : Wn i < E := by
            rw [hWn i hi]
            exact (hAB ⟨i, hi⟩).mpr ⟨hiA, hiB⟩
          exact le_of_lt (hstep_down i hi hlt)
        have hright : ∀ (i : ℕ) (hi : i < ℓ), B < i → slope ψ i ≤ slope ψ (i + 1) := by
          intro i hi hiB
          by_cases hlt : W ⟨i, hi⟩ < E
          · exact absurd (by simpa using ((hAB ⟨i, hi⟩).mp hlt).2) (by omega)
          · push Not at hlt
            rcases lt_or_eq_of_le hlt with hgt | heq
            · exact le_of_lt (hstep_up i hi (by rw [hWn i hi]; exact hgt))
            · have hstep_flat : slope ψ i = slope ψ (i + 1) := by
                have hr := hrecN i hi
                rw [heq] at hr
                have hz : slope ψ (i + 1) - slope ψ i = 0 := by simpa using hr
                linarith
              exact le_of_eq hstep_flat
        have hnonneg : ∀ i, i ≤ A → 0 ≤ slope ψ i := by
          intro i hi
          have hmono := mono_le (f := slope ψ) (lo := 0) (hi := A)
            (fun k _ hk => hleft k (by omega) hk) 0 i (by omega) (by omega) (by omega)
          rwa [slope_zero] at hmono
        have hnonpos : ∀ i, B + 1 ≤ i → i ≤ ℓ → slope ψ i ≤ 0 := by
          intro i hi1 hi2
          have hmono := mono_le (f := slope ψ) (lo := B + 1) (hi := ℓ)
            (fun k hk1 _ => hright k (by omega) (by omega)) i ℓ hi1 hi2 le_rfl
          rwa [slope_last h0] at hmono
        have fall_exists : ∀ (lo hi : ℕ), lo ≤ hi → hi ≤ ℓ → 0 < slope ψ lo → slope ψ hi ≤ 0 →
            ∃ k, lo ≤ k ∧ k < hi ∧ slope ψ (k + 1) < slope ψ k := by
          intro lo hi hlth hhi h1 h2
          by_contra hcon
          push Not at hcon
          have hmono : slope ψ lo ≤ slope ψ hi :=
            mono_le (f := slope ψ) (lo := lo) (hi := hi) hcon lo hi le_rfl (by omega)
              (by omega)
          linarith
        -- a crossing of the slope cannot be followed by a gap
        have prop_gap : ∀ (p q : ℕ), p + 1 < ℓ → 0 ≤ slope ψ p → slope ψ (p + 1) ≤ 0 →
            ¬ (0 ≤ slope ψ (p + 1) ∧ slope ψ (p + 2) ≤ 0) → p < q → q < ℓ →
            ¬ (0 ≤ slope ψ q ∧ slope ψ (q + 1) ≤ 0) := by
          intro p q hpℓ hp1 hp2 hpgap hpq hqℓ hqC
          by_cases hneg : slope ψ (p + 1) < 0
          · have hpℓ' : p < ℓ := by omega
            have hWp : Wn p < E := by
              rw [hWn p hpℓ']
              have hr := hrecN p hpℓ'
              have hpp : 0 < ψ ⟨p, hpℓ'⟩ := hpos _
              nlinarith [hr, hpp]
            have hex : ∃ r : ℕ, p + 1 ≤ r ∧ r ≤ q ∧ 0 ≤ slope ψ r :=
              ⟨q, by omega, le_rfl, hqC.1⟩
            have hr1 : p + 1 ≤ Nat.find hex := (Nat.find_spec hex).1
            have hr2 : Nat.find hex ≤ q := (Nat.find_spec hex).2.1
            have hr3 : 0 ≤ slope ψ (Nat.find hex) := (Nat.find_spec hex).2.2
            have hrmin : ∀ m, m < Nat.find hex → ¬ (p + 1 ≤ m ∧ m ≤ q ∧ 0 ≤ slope ψ m) := by
              intro m hm hpm
              exact absurd (Nat.find_min' hex hpm) (by omega)
            have hrge : p + 2 ≤ Nat.find hex := by
              rcases Nat.lt_or_ge (Nat.find hex) (p + 2) with hlt | hge
              · have hfe : Nat.find hex = p + 1 := by omega
                rw [hfe] at hr3
                linarith
              · exact hge
            have hjneg : slope ψ (Nat.find hex - 1) < 0 := by
              by_contra hc
              push Not at hc
              exact hrmin (Nat.find hex - 1) (by omega) ⟨by omega, by omega, hc⟩
            have hrise : slope ψ (Nat.find hex - 1) < slope ψ (Nat.find hex) := by
              have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
              have hr3' : (0 : ℝ) ≤ slope ψ (Nat.find hex - 1 + 1) := by
                rw [heq]
                exact hr3
              linarith
            have hWj : E < Wn (Nat.find hex - 1) := by
              have hbℓ : Nat.find hex - 1 < ℓ := by omega
              rw [hWn (Nat.find hex - 1) hbℓ]
              have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
              have hr := hrecN (Nat.find hex - 1) hbℓ
              rw [heq] at hr
              have hpj : 0 < ψ ⟨Nat.find hex - 1, hbℓ⟩ := hpos _
              nlinarith [hr, hpj, hrise]
            by_cases hfall : ∃ k, Nat.find hex ≤ k ∧ k ≤ q ∧ slope ψ (k + 1) < slope ψ k
            · obtain ⟨k, hk1, hk2, hk3⟩ := hfall
              have hkℓ : k < ℓ := by omega
              have hWk : Wn k < E := by
                rw [hWn k hkℓ]
                have hr := hrecN k hkℓ
                have hpk : 0 < ψ ⟨k, hkℓ⟩ := hpos _
                nlinarith [hr, hpk]
              have hmax := hqc p (Nat.find hex - 1) k hpℓ' (by omega) hkℓ (by omega) (by omega)
              linarith [max_lt hWp hWk]
            · push Not at hfall
              have hflat : slope ψ (Nat.find hex) ≤ slope ψ (q + 1) :=
                mono_le (f := slope ψ) (lo := Nat.find hex) (hi := q + 1)
                  (fun k hk1 hk2 => hfall k hk1 (by omega)) (Nat.find hex)
                  (q + 1) le_rfl (by omega) (by omega)
              have hz : slope ψ (Nat.find hex) = 0 := by linarith [hflat, hqC.2, hr3]
              have hz2 : slope ψ (Nat.find hex + 1) = 0 := by
                have h2 : slope ψ (Nat.find hex) ≤ slope ψ (Nat.find hex + 1) :=
                  hfall (Nat.find hex) le_rfl (by omega)
                have h3 : slope ψ (Nat.find hex + 1) ≤ slope ψ (q + 1) :=
                  mono_le (f := slope ψ) (lo := Nat.find hex + 1) (hi := q + 1)
                    (fun k hk1 hk2 => hfall k (by omega) (by omega))
                    (Nat.find hex + 1) (q + 1) le_rfl (by omega) (by omega)
                linarith [hqC.2]
              have hWE : Wn (Nat.find hex) = E := by
                have hbℓ : Nat.find hex < ℓ := by omega
                rw [hWn (Nat.find hex) hbℓ]
                have hr := hrecN (Nat.find hex) hbℓ
                have hp : 0 < ψ ⟨Nat.find hex, hbℓ⟩ := hpos _
                rw [hz2, hz] at hr
                have hmul : (W ⟨Nat.find hex, hbℓ⟩ - E) * ψ ⟨Nat.find hex, hbℓ⟩ = 0 := by
                  linarith
                rcases mul_eq_zero.mp hmul with h1 | h2
                · linarith
                · exact absurd h2 hp.ne'
              have hmax := hqc p (Nat.find hex - 1) (Nat.find hex) hpℓ' (by omega) (by omega)
                (by omega) (by omega)
              rw [hWE, max_eq_right (le_of_lt hWp)] at hmax
              linarith
          · push Not at hneg
            have hz : slope ψ (p + 1) = 0 := le_antisymm hp2 hneg
            have hpos2 : 0 < slope ψ (p + 2) := by
              by_contra hc
              push Not at hc
              exact hpgap ⟨hneg, hc⟩
            have hW1 : E < W ⟨p + 1, hpℓ⟩ := by
              have hr : slope ψ (p + 2) - slope ψ (p + 1) =
                  (W ⟨p + 1, hpℓ⟩ - E) * ψ ⟨p + 1, hpℓ⟩ := by
                have heq : p + 1 + 1 = p + 2 := by omega
                rw [← heq]
                exact hrecN (p + 1) hpℓ
              have hp1ψ : 0 < ψ ⟨p + 1, hpℓ⟩ := hpos _
              nlinarith [hr, hp1ψ]
            by_cases hle : p + 1 ≤ A
            · have hz1 : slope ψ 1 = 0 := by
                have hz0 : slope ψ 0 ≤ slope ψ 1 :=
                  mono_le (f := slope ψ) (lo := 0) (hi := A)
                    (fun k _ hk => hleft k (by omega) hk) 0 1 (by omega) (by omega) (by omega)
                have hz1' : slope ψ 1 ≤ slope ψ (p + 1) :=
                  mono_le (f := slope ψ) (lo := 0) (hi := A)
                    (fun k _ hk => hleft k (by omega) hk) 1 (p + 1) (by omega) (by omega)
                    (by omega)
                rw [slope_zero] at hz0
                rw [hz] at hz1'
                linarith
              have hW0 : Wn 0 = E := by
                rw [hWn 0 h0]
                have hr := hrecN 0 h0
                have hp0 : 0 < ψ ⟨0, h0⟩ := hpos _
                simp only [Nat.zero_add] at hr
                rw [slope_zero, hz1] at hr
                have hmul : (W ⟨0, h0⟩ - E) * ψ ⟨0, h0⟩ = 0 := by linarith
                rcases mul_eq_zero.mp hmul with h1 | h2
                · linarith
                · exact absurd h2 hp0.ne'
              obtain ⟨k, hk1, hk2, hk3⟩ :=
                fall_exists (p + 2) (q + 1) (by omega) (by omega) hpos2 (by linarith [hqC.2])
              have hkℓ : k < ℓ := by omega
              have hWk : Wn k < E := by
                rw [hWn k hkℓ]
                have hr := hrecN k hkℓ
                have hpk : 0 < ψ ⟨k, hkℓ⟩ := hpos _
                nlinarith [hr, hpk]
              have hW1n : E < Wn (p + 1) := by rw [hWn (p + 1) hpℓ]; exact hW1
              have hmax := hqc 0 (p + 1) k h0 hpℓ hkℓ (by omega) (by omega)
              rw [hW0] at hmax
              rw [max_eq_left (le_of_lt hWk)] at hmax
              linarith
            · have hgt : B < p + 1 := by
                by_contra hc
                push Not at hc
                have hmem : A ≤ (⟨p + 1, hpℓ⟩ : Fin ℓ).val ∧ (⟨p + 1, hpℓ⟩ : Fin ℓ).val ≤ B := by
                  dsimp only [Fin.val_mk]
                  omega
                exact absurd ((hAB ⟨p + 1, hpℓ⟩).mpr hmem) (by linarith)
              have hmono := hnonpos (p + 2) (by omega) (by omega)
              linarith
        have hstep : ∀ t : ℕ, x.val ≤ t → t + 1 ≤ y.val →
            (0 ≤ slope ψ t ∧ slope ψ (t + 1) ≤ 0) →
            (0 ≤ slope ψ (t + 1) ∧ slope ψ (t + 2) ≤ 0) := by
          intro t hxt hty hC
          by_contra hnc
          exact (prop_gap t z.val (by omega) hC.1 hC.2 hnc (by omega) z.isLt) ⟨hz1, hz2⟩
        have key : ∀ t : ℕ, x.val ≤ t → t ≤ y.val → 0 ≤ slope ψ t ∧ slope ψ (t + 1) ≤ 0 := by
          intro t hxt
          induction t, hxt using Nat.le_induction with
          | base => intro _; exact ⟨hx1, hx2⟩
          | succ t hxt ih => intro hty; exact hstep t hxt (by omega) (ih (by omega))
        exact key y.val hxy le_rfl
      · push Not at hne
        have hmono_all : ∀ i, i < ℓ → slope ψ i ≤ slope ψ (i + 1) := by
          intro i hi
          rcases lt_or_eq_of_le (hne ⟨i, hi⟩) with hgt | heq
          · exact le_of_lt (hstep_up i hi (by rw [hWn i hi]; exact hgt))
          · have hstep_flat : slope ψ i = slope ψ (i + 1) := by
              have hr := hrecN i hi
              rw [heq] at hr
              have hz : slope ψ (i + 1) - slope ψ i = 0 := by simpa using hr
              linarith
            exact le_of_eq hstep_flat
        have hzero_all : ∀ i, i ≤ ℓ → slope ψ i = 0 := by
          intro i hi
          have h1 : slope ψ 0 ≤ slope ψ i :=
            mono_le (f := slope ψ) (lo := 0) (hi := ℓ)
              (fun k _ hk => hmono_all k hk) 0 i (by omega) (by omega) (by omega)
          have h2 : slope ψ i ≤ slope ψ ℓ :=
            mono_le (f := slope ψ) (lo := 0) (hi := ℓ)
              (fun k _ hk => hmono_all k hk) i ℓ (by omega) (by omega) (by omega)
          rw [slope_zero] at h1
          rw [slope_last h0] at h2
          linarith
        refine ⟨?_, ?_⟩
        · rw [hzero_all y.val (by omega)]
        · rw [hzero_all (y.val + 1) (by omega)]
    have hloc : ∀ x : Fin ℓ, IsLocalMax (SimpleGraph.pathGraph ℓ) ψ x →
        0 ≤ slope ψ x.val ∧ slope ψ (x.val + 1) ≤ 0 := fun x hx => (hcross x).mp hx
    have hloc' : ∀ x : Fin ℓ, 0 ≤ slope ψ x.val → slope ψ (x.val + 1) ≤ 0 →
        IsLocalMax (SimpleGraph.pathGraph ℓ) ψ x := fun x h1 h2 => (hcross x).mpr ⟨h1, h2⟩
    have hconvex : ∀ x y z : Fin ℓ, x ≤ y → y ≤ z →
        IsLocalMax (SimpleGraph.pathGraph ℓ) ψ x → IsLocalMax (SimpleGraph.pathGraph ℓ) ψ z →
        IsLocalMax (SimpleGraph.pathGraph ℓ) ψ y := by
      intro x y z hxy hyz hx hz
      obtain ⟨h1, h2⟩ :=
        hconv_cross x y z hxy hyz (hloc x hx).1 (hloc x hx).2 (hloc z hz).1 (hloc z hz).2
      exact hloc' y h1 h2
    show ((SimpleGraph.pathGraph ℓ).induce
      {x : Fin ℓ | IsLocalMax (SimpleGraph.pathGraph ℓ) ψ x}).Preconnected
    intro u v
    rcases le_total u.1 v.1 with hle | hle
    · exact reachable_induce_of_convex hconvex hle
    · exact (reachable_induce_of_convex hconvex hle).symm

end Qatlib.Papers.AdiabNoLocMin14.MainResults
