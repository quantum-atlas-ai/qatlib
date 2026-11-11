/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false

/-!
# Coupling-matrix sparsity in the Daubechies wavelet basis

Fixed paper version: arXiv:1412.0750v1 (2 Dec 2014), Brennen--Rohde--Sanders--Singh,
*Multi-scale quantum simulation of quantum field theory using wavelets*.

Source statement (Sec. III, p. 6, immediately after Eq. (30)):

> Because the wavelets have compact support, the coupling matrix is sparse having
> ≃ 10 V log(V) non zero elements, with the factor of 10 arising from the fact that
> Daubechies K wavelets have overlap with 2(2K − 1) translates within any given scale.

This file builds the finite mode model of the paper's 1-dimensional construction
(Eq. (26): `V = L · 2^(lmax + 1)`; Eq. (30): scale block `Kss` of size `L × L`,
scale--wavelet blocks `Ksw(l)` of size `L × L·2^l`, wavelet--wavelet blocks
`Kww(l,j)`) and proves that the number of mode pairs whose compact supports
intersect is at most `10 · V · (lmax + 2)`.  For the paper's choice `K = 3`
(Daubechies 6-tap, all numerical figures) the within-scale overlap
`2(2K−1) = 10` is exactly the paper's factor `10`; the extra `(lmax + 2)` is the
number of dyadic levels, i.e. `log₂ V + O(1)`.

Boundary: this is the combinatorial support count only.  It does not evaluate the
overlap integrals of Eq. (32)--(34), does not assert that every overlapping pair
has a nonzero integral (that is a property of the Daubechies filter, used as an
upper-bound relaxation here), and does not model the quartic interaction block of
Eq. (47), which the paper counts by the same compact-support argument.

Reference comparison: no wavelet declaration exists in `QuantumAlgorithmDev/` or in
the Frozen package `qatlas_frozen/QuantumAlgorithm/` (checked by `rg -i
"wavelet|daubechies|MERA"`), so this Block necessarily defines the mode model.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.WaveletQFT14.MainResults.CouplingSparsity

attribute [local instance] Classical.propDecidable

/-- Support width of a Daubechies `K = 3` wavelet in translate units: `2K − 1 = 5`.
The paper's factor `2(2K − 1) = 10` is `2 * supportWidth`. -/
def supportWidth : ℕ := 5

/-- A mode of the paper's 1-dimensional wavelet register (Eq. (26) and Eq. (30)).

* `scale a` is one of the `L` level-`lmin` scale functions `s^lmin_a`.
* `wavelet e n` is the translate `n` of the wavelet at dyadic level `e`
  (`e = 0` is level `l = lmin`, `e` counts upward to `lmax`); level `e` carries
  `L · 2^e` translates.

The total number of modes is `L + Σ_{e<lmax+1} L·2^e = L·2^(lmax+1) = V`. -/
inductive Mode (L lmax : ℕ) where
  | scale (a : Fin L)
  | wavelet (e : Fin (lmax + 1)) (n : Fin (L * 2 ^ (e : ℕ)))
  deriving DecidableEq, Fintype

namespace Mode

variable {L lmax : ℕ}

/-- Dyadic level: scale functions sit at level `0`, wavelets at level `e + 1`.
Levels therefore range over `0, …, lmax + 1`. -/
def level : Mode L lmax → ℕ
  | .scale _ => 0
  | .wavelet e _ => (e : ℕ) + 1

/-- Translate index within the mode's own level (`a` for a scale function,
`n` for a wavelet). -/
def index : Mode L lmax → ℕ
  | .scale a => (a : ℕ)
  | .wavelet _ n => (n : ℕ)

/-- Lattice spacing of the mode's level, in units of the finest grid: a level-`l`
mode has spacing `2^(lmax + 1 − l)`.  This is `2^(lmax+1)` for scale functions
(level `0`) and `2^(lmax−e)` for the wavelet level `e` (level `e+1`), matching
Eq. (30) of the paper. -/
def spacing (u : Mode L lmax) : ℕ := 2 ^ (lmax + 1 - u.level)

/-- Left endpoint of the compact support on the finest grid. -/
def start (u : Mode L lmax) : ℕ := u.index * u.spacing

/-- Width of the compact support: Daubechies `K = 3` has `2K − 1 = 5` translates
of support. -/
def span (u : Mode L lmax) : ℕ := supportWidth * u.spacing

/-- The lattice spacing of every mode is positive. -/
lemma spacing_pos (u : Mode L lmax) : 0 < u.spacing := by
  unfold spacing; positivity

/-- Every mode has a support of positive width. -/
lemma span_pos (u : Mode L lmax) : 0 < u.span := by
  unfold span; have := u.spacing_pos; unfold supportWidth; omega

/-- Every mode lies at or below the finest wavelet level. -/
lemma level_le (u : Mode L lmax) : u.level ≤ lmax + 1 := by
  cases u with
  | scale _ => simp [level]
  | wavelet e _ => simp only [level]; omega

/-- The mode is determined by its level together with its translate index. -/
lemma ext_level_index {u v : Mode L lmax} (hlev : u.level = v.level) (hidx : u.index = v.index) :
    u = v := by
  cases u with
  | scale a =>
      cases v with
      | scale b => simp only [index, Fin.val_inj] at hidx; subst hidx; rfl
      | wavelet e n => simp [level] at hlev
  | wavelet e n =>
      cases v with
      | scale b => simp [level] at hlev
      | wavelet e' n' =>
          have hev : (e : ℕ) = (e' : ℕ) := by
            simp only [level, Nat.add_right_cancel_iff] at hlev; exact hlev
          have he : e = e' := Fin.ext hev
          subst he
          have hnv : (n : ℕ) = (n' : ℕ) := by
            simpa only [index, Fin.val_inj] using hidx
          exact congrArg (fun x => Mode.wavelet e x) (Fin.ext hnv)

/-- Spacing of a wavelet at level `e`. -/
lemma spacing_wavelet {e : Fin (lmax + 1)} {n : Fin (L * 2 ^ (e : ℕ))} :
    (wavelet e n).spacing = 2 ^ (lmax - (e : ℕ)) := by
  simp only [spacing, level]
  congr 1
  omega

end Mode

open Mode

/-- Two modes couple when their compact supports overlap (share a finest-grid cell). -/
def Overlaps {L lmax : ℕ} (u v : Mode L lmax) : Prop :=
  u.start < v.start + v.span ∧ v.start < u.start + u.span

/-- The off-diagonal coupling pattern: ordered pairs of modes with overlapping
support, each pair counted once by orienting it from the coarser to the finer
mode (ties broken arbitrarily but consistently by `level u ≤ level v`). -/
def nonzeroCouplings (L lmax : ℕ) : Finset (Mode L lmax × Mode L lmax) := by
  classical
  exact Finset.univ.filter (fun p : Mode L lmax × Mode L lmax =>
    Overlaps p.1 p.2 ∧ p.1.level ≤ p.2.level)

/-- Number of modes `V = L · 2^(lmax+1)` (Eq. (26) of the paper). -/
def numModes (L lmax : ℕ) : ℕ := L * 2 ^ (lmax + 1)

/-- A mode translate index is smaller than the total number of modes. -/
lemma index_lt_numModes {L lmax : ℕ} (u : Mode L lmax) : u.index < numModes L lmax := by
  cases u with
  | scale a =>
      simp only [index, numModes]
      calc (a : ℕ) < L := a.isLt
        _ ≤ L * 2 ^ (lmax + 1) := Nat.le_mul_of_pos_right L (by positivity)
  | wavelet e n =>
      simp only [index, numModes]
      calc (n : ℕ) < L * 2 ^ (e : ℕ) := n.isLt
        _ ≤ L * 2 ^ (lmax + 1) := by
            apply Nat.mul_le_mul_left
            apply Nat.pow_le_pow_right (by norm_num)
            have := e.isLt; omega

/-! ## Counting lemmas on initial segments of `ℕ` -/

/-- If all elements of a finite set of natural numbers differ from each other by at
most `d`, then the set has at most `d + 1` elements. -/
lemma card_le_succ_of_max_sub_le (S : Finset ℕ) (d : ℕ)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → b - a ≤ d) : S.card ≤ d + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S a ha, Finset.le_max' S a ha⟩
    have hmin : S.min' hne ∈ S := Finset.min'_mem S hne
    have hmax : S.max' hne ∈ S := Finset.max'_mem S hne
    have hle : S.min' hne ≤ S.max' hne := Finset.min'_le S _ hmax
    have hdiff : S.max' hne - S.min' hne ≤ d := h _ hmin _ hmax hle
    calc S.card ≤ (Finset.Icc (S.min' hne) (S.max' hne)).card := Finset.card_le_card hsub
      _ = S.max' hne + 1 - S.min' hne := Nat.card_Icc _ _
      _ = S.max' hne - S.min' hne + 1 := by omega
      _ ≤ d + 1 := Nat.add_le_add_right hdiff 1

/-- Same-level index window: if two indices both lie within distance `< 5` of a
fixed index `n`, their difference is at most `8`; hence at most `9` of them occur. -/
lemma card_sameLevel_index (N n : ℕ) :
    ((Finset.range N).filter (fun a => a < n + 5 ∧ n < a + 5)).card ≤ 9 := by
  classical
  refine card_le_succ_of_max_sub_le _ 8 ?_
  intro a ha b hb hab
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  omega

/-- Coarser-level index window: indices `a` with `a · 2^t < n + 5` and
`n < (a + 5) · 2^t` (with `t ≥ 1`) differ from each other by at most `8`, so at
most `9` occur.  This is the translate-level count behind the `O(V log V)` term. -/
lemma card_crossLevel_index (N n t : ℕ) (ht : 1 ≤ t) :
    ((Finset.range N).filter
        (fun a => a * 2 ^ t < n + 5 ∧ n < (a + 5) * 2 ^ t)).card ≤ 9 := by
  classical
  refine card_le_succ_of_max_sub_le _ 8 ?_
  intro a ha b hb hab
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  by_contra hcon
  push Not at hcon
  have hba : a + 9 ≤ b := by omega
  have hp : 2 ≤ 2 ^ t := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have h1 : b * 2 ^ t < n + 5 := hb.2.1
  have h2 : n < (a + 5) * 2 ^ t := ha.2.2
  have h3 : b * 2 ^ t < (a + 5) * 2 ^ t + 5 := by omega
  have h9 : (a + 9) * 2 ^ t ≤ b * 2 ^ t := Nat.mul_le_mul_right _ hba
  have hsplit : (a + 9) * 2 ^ t = a * 2 ^ t + 9 * 2 ^ t := by rw [Nat.add_mul]
  have hsplit2 : (a + 5) * 2 ^ t + 5 = a * 2 ^ t + (5 * 2 ^ t + 5) := by
    rw [Nat.add_mul]; omega
  have hlt : a * 2 ^ t + 9 * 2 ^ t < a * 2 ^ t + (5 * 2 ^ t + 5) := by
    calc a * 2 ^ t + 9 * 2 ^ t = (a + 9) * 2 ^ t := hsplit.symm
      _ ≤ b * 2 ^ t := h9
      _ < (a + 5) * 2 ^ t + 5 := h3
      _ = a * 2 ^ t + (5 * 2 ^ t + 5) := hsplit2
  have h8 : 9 * 2 ^ t < 5 * 2 ^ t + 5 := Nat.add_lt_add_iff_left.mp hlt
  nlinarith [hp, h8]

/-! ## Index inequalities implied by support overlap -/

/-- Same-level overlap forces the translate indices to be within `5`. -/
lemma index_lt_of_overlap_same_level {L lmax : ℕ} {u v : Mode L lmax} (hl : u.level = v.level)
    (hov : Overlaps u v) :
    u.index < v.index + 5 ∧ v.index < u.index + 5 := by
  unfold Overlaps at hov
  have hsp : u.spacing = v.spacing := by
    unfold Mode.spacing; rw [hl]
  have hD : 0 < v.spacing := v.spacing_pos
  have e1 : u.start < v.start + v.span := hov.1
  have e2 : v.start < u.start + u.span := hov.2
  simp only [Mode.start, Mode.span, supportWidth] at e1 e2
  rw [hsp] at e1 e2
  have e1' : u.index * v.spacing < (v.index + 5) * v.spacing := by
    rw [Nat.add_mul]; exact e1
  have e2' : v.index * v.spacing < (u.index + 5) * v.spacing := by
    rw [Nat.add_mul]; exact e2
  exact ⟨(Nat.mul_lt_mul_right hD).mp e1', (Nat.mul_lt_mul_right hD).mp e2'⟩

/-- Cross-level overlap (`u` coarser than `v`) forces the translate indices into a
window of length `5 · (2^t + 1)` scaled by `2^t`, `t = level v − level u ≥ 1`. -/
lemma index_lt_of_overlap_cross_level {L lmax : ℕ} {u v : Mode L lmax} (hlt : u.level < v.level)
    (hov : Overlaps u v) :
    u.index * 2 ^ (v.level - u.level) < v.index + 5 ∧
      v.index < (u.index + 5) * 2 ^ (v.level - u.level) := by
  unfold Overlaps at hov
  set t := v.level - u.level
  have ht1 : 1 ≤ t := by omega
  have hsp : u.spacing = 2 ^ t * v.spacing := by
    unfold Mode.spacing
    have hexp : lmax + 1 - u.level = (lmax + 1 - v.level) + (v.level - u.level) := by
      have h1 := u.level_le; have h2 := v.level_le; omega
    rw [hexp, Nat.pow_add]
    ring
  have hD : 0 < v.spacing := v.spacing_pos
  have e1 : u.start < v.start + v.span := hov.1
  have e2 : v.start < u.start + u.span := hov.2
  simp only [Mode.start, Mode.span, supportWidth] at e1 e2
  rw [hsp] at e1 e2
  constructor
  · have e1' : (u.index * 2 ^ t) * v.spacing < (v.index + 5) * v.spacing := by
      rw [Nat.mul_assoc, Nat.add_mul]
      exact e1
    exact (Nat.mul_lt_mul_right hD).mp e1'
  · have e2' : v.index * v.spacing < ((u.index + 5) * 2 ^ t) * v.spacing := by
      rw [Nat.mul_assoc, Nat.add_mul]
      exact e2
    exact (Nat.mul_lt_mul_right hD).mp e2'

/-! ## Per-level slice bound -/

/-- Fix a finer mode `v` and a level `l ≤ level v`.  The modes of level `l` that
overlap `v` number at most `9` (the `2(2K−1)`-style window at `K = 3`). -/
lemma card_slice_le {L lmax : ℕ} (l : ℕ) (v : Mode L lmax) (hlv : l ≤ v.level) :
    ((Finset.univ : Finset (Mode L lmax)).filter
        (fun u => u.level = l ∧ Overlaps u v)).card ≤ 9 := by
  classical
  set S := (Finset.univ : Finset (Mode L lmax)).filter
      (fun u => u.level = l ∧ Overlaps u v) with hS
  have hinj : Set.InjOn (fun u : Mode L lmax => u.index) (↑S : Set (Mode L lmax)) := by
    intro u hu w hw hidx
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hu hw
    exact Mode.ext_level_index (hu.2.1.trans hw.2.1.symm) hidx
  have hcard : S.card = (S.image (fun u => u.index)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  rcases eq_or_lt_of_le hlv with heq | hlt
  · -- same level
    subst heq
    apply le_trans _ (card_sameLevel_index (numModes L lmax) v.index)
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    rw [hS, Finset.mem_filter] at hu
    obtain ⟨hlev, hov⟩ := hu.2
    have h := index_lt_of_overlap_same_level (u := u) (v := v) hlev hov
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (index_lt_numModes u), h.1, h.2⟩
  · -- coarser level
    apply le_trans _ (card_crossLevel_index (numModes L lmax) v.index (v.level - l) (by omega))
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    rw [hS, Finset.mem_filter] at hu
    obtain ⟨hlev, hov⟩ := hu.2
    have hlt_uv : u.level < v.level := by rw [hlev]; exact hlt
    have h := index_lt_of_overlap_cross_level (u := u) (v := v) hlt_uv hov
    rw [hlev] at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (index_lt_numModes u), h.1, h.2⟩

/-- Fiber bound: for a fixed finer mode `v`, at most `9 · (lmax + 2)` coarser or
equal modes overlap it (one level budget of `9` per dyadic level). -/
lemma card_fiber_le {L lmax : ℕ} (v : Mode L lmax) :
    ((Finset.univ : Finset (Mode L lmax)).filter
        (fun u => u.level ≤ v.level ∧ Overlaps u v)).card ≤ 9 * (lmax + 2) := by
  classical
  set S := (Finset.univ : Finset (Mode L lmax)).filter
      (fun u => u.level ≤ v.level ∧ Overlaps u v) with hS
  have hsub : S ⊆ (Finset.range (lmax + 2)).biUnion (fun l => S.filter (fun u => u.level = l)) := by
    intro u hu
    rw [Finset.mem_biUnion]
    refine ⟨u.level, ?_, ?_⟩
    · rw [Finset.mem_range]; have := u.level_le; omega
    · rw [Finset.mem_filter]; exact ⟨hu, rfl⟩
  have hb : ∀ l ∈ Finset.range (lmax + 2), (S.filter (fun u => u.level = l)).card ≤ 9 := by
    intro l hl
    rw [Finset.mem_range] at hl
    by_cases hlv : l ≤ v.level
    · apply le_trans _ (card_slice_le l v hlv)
      apply Finset.card_le_card
      intro u hu
      rw [Finset.mem_filter, hS, Finset.mem_filter] at hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2, hu.1.2.2⟩
    · have hempty : S.filter (fun u => u.level = l) = ∅ := by
        apply Finset.filter_false_of_mem
        intro u hu
        rw [Finset.mem_filter] at hu
        omega
      rw [hempty]; simp
  calc S.card ≤ ((Finset.range (lmax + 2)).biUnion (fun l => S.filter (fun u => u.level = l))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ l ∈ Finset.range (lmax + 2), (S.filter (fun u => u.level = l)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ Finset.range (lmax + 2), 9 := Finset.sum_le_sum hb
    _ = 9 * (lmax + 2) := by simp [Finset.sum_const, Nat.mul_comm]

/-! ## Global count -/

/-- Sum over the second coordinate of a product-type relation bounds the relation. -/
lemma card_filter_prod_le_sum {α β : Type} [Fintype α] [Fintype β]
    (R : α → β → Prop) [DecidableRel R] :
    (Finset.univ.filter (fun p : α × β => R p.1 p.2)).card ≤
      ∑ v : β, (Finset.univ.filter (fun u : α => R u v)).card := by
  classical
  have hsub : (Finset.univ.filter (fun p : α × β => R p.1 p.2)) ⊆
      Finset.univ.biUnion (fun v : β =>
        (Finset.univ.filter (fun u : α => R u v)).image (fun u => (u, v))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_biUnion]
    refine ⟨p.2, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩
  calc (Finset.univ.filter (fun p : α × β => R p.1 p.2)).card
      ≤ (Finset.univ.biUnion (fun v : β =>
          (Finset.univ.filter (fun u : α => R u v)).image (fun u => (u, v)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v : β, ((Finset.univ.filter (fun u : α => R u v)).image (fun u => (u, v))).card :=
        Finset.card_biUnion_le
    _ = ∑ v : β, (Finset.univ.filter (fun u : α => R u v)).card := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)

/-- `∑_{e < n} 2^e = 2^n − 1`. -/
lemma sum_range_pow_two (n : ℕ) : (∑ e ∈ Finset.range n, 2 ^ e) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega

/-- Card of the mode type: `V = L · 2^(lmax+1)` (Eq. (26)). -/
lemma card_mode (L lmax : ℕ) : Fintype.card (Mode L lmax) = numModes L lmax := by
  have hsum : (∑ e : Fin (lmax + 1), L * 2 ^ (e : ℕ)) = L * (2 ^ (lmax + 1) - 1) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun e => 2 ^ e), Finset.sum_range_succ,
      sum_range_pow_two]
    have h2 : 2 ^ (lmax + 1) = 2 ^ lmax + 2 ^ lmax := by
      rw [pow_succ]; ring
    have : 1 ≤ 2 ^ lmax := Nat.one_le_pow lmax 2 (by norm_num)
    omega
  -- explicit bijection with the sum type
  let f : Mode L lmax → Fin L ⊕ (Σ e : Fin (lmax + 1), Fin (L * 2 ^ (e : ℕ)))
    | .scale a => Sum.inl a
    | .wavelet e n => Sum.inr ⟨e, n⟩
  let g : Fin L ⊕ (Σ e : Fin (lmax + 1), Fin (L * 2 ^ (e : ℕ))) → Mode L lmax
    | Sum.inl a => .scale a
    | Sum.inr s => .wavelet s.1 s.2
  have hleft : ∀ x, g (f x) = x := by intro x; cases x <;> rfl
  have hright : ∀ x, f (g x) = x := by
    intro x; cases x with
    | inl a => rfl
    | inr s => cases s; rfl
  have heq : Mode L lmax ≃ (Fin L ⊕ (Σ e : Fin (lmax + 1), Fin (L * 2 ^ (e : ℕ)))) :=
    ⟨f, g, hleft, hright⟩
  rw [Fintype.card_congr heq, Fintype.card_sum, Fintype.card_sigma]
  simp only [Fintype.card_fin, hsum, numModes]
  -- `L + L * (2^(lmax+1) - 1) = L * 2^(lmax+1)`
  have hpos : 1 ≤ 2 ^ (lmax + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hexp : L * (2 ^ (lmax + 1) - 1) = L * 2 ^ (lmax + 1) - L := by
    rw [Nat.mul_sub, Nat.mul_one]
  have hLt : L ≤ L * 2 ^ (lmax + 1) := Nat.le_mul_of_pos_right L (by positivity)
  rw [hexp]
  omega

/-- **c002 (source: Sec. III, p. 6, below Eq. (30))**.  With `V = L·2^(lmax+1)`
modes, the number of ordered mode pairs with overlapping compact support — hence
the sparsity pattern of the coupling matrix `K` of Eq. (30) after the upper-bound
relaxation that every overlapping pair may contribute — is at most
`10 · V · (lmax + 2)`, i.e. `≃ 10 V log V`.  The factor `10 = 2(2K−1)` at `K = 3`
is the paper's within-scale overlap count. -/
theorem source_coupling_sparsity (L lmax : ℕ) :
    (nonzeroCouplings L lmax).card ≤ 10 * numModes L lmax * (lmax + 2) := by
  classical
  have hmain := card_filter_prod_le_sum
    (fun u v : Mode L lmax => u.level ≤ v.level ∧ Overlaps u v)
  have heq : nonzeroCouplings L lmax =
      Finset.univ.filter (fun p : Mode L lmax × Mode L lmax =>
        p.1.level ≤ p.2.level ∧ Overlaps p.1 p.2) := by
    rw [nonzeroCouplings]
    apply Finset.filter_congr
    intro p _
    exact and_comm
  rw [heq]
  refine le_trans hmain ?_
  have hb : ∀ v : Mode L lmax,
      (Finset.univ.filter (fun u : Mode L lmax => u.level ≤ v.level ∧ Overlaps u v)).card
        ≤ 9 * (lmax + 2) := card_fiber_le
  calc ∑ v : Mode L lmax,
        (Finset.univ.filter (fun u : Mode L lmax => u.level ≤ v.level ∧ Overlaps u v)).card
      ≤ ∑ _v : Mode L lmax, 9 * (lmax + 2) := Finset.sum_le_sum (fun v _ => hb v)
    _ = Fintype.card (Mode L lmax) * (9 * (lmax + 2)) := by
        simp [Finset.sum_const]
    _ = numModes L lmax * (9 * (lmax + 2)) := by rw [card_mode]
    _ ≤ 10 * numModes L lmax * (lmax + 2) := by
        rw [show 10 * numModes L lmax * (lmax + 2) =
          numModes L lmax * (10 * (lmax + 2)) by ring]
        apply Nat.mul_le_mul_left
        omega

/-- The paper's numerical factor: `2(2K − 1)` at `K = 3`. -/
theorem factor_ten : 2 * (2 * 3 - 1) = 10 := by norm_num

end Qatlib.Papers.WaveletQFT14.MainResults.CouplingSparsity
