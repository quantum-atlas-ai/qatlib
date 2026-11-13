/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SphericalColumn — the canonical `U_ψ` of the quantum Viterbi algorithm

Grice--Meyer, *A quantum algorithm for Viterbi decoding of classical convolutional
codes*, fixed arXiv:1405.7479v2 (PDF dated 2015-06-20), Section 2.3, Eq. (8) and the
induction proved between Eq. (8) and Eq. (9) on printed pp. 7-8.

The source needs a unitary `U_ψ : |0⟩ ↦ |ψ⟩` on `C^{K+1}` for the fanout vector of an
HMM state. Its canonical construction is the product

`V = R_y(θ_1)_{|0⟩,|1⟩} R_y(θ_2)_{|0⟩,|2⟩} ⋯ R_y(θ_K)_{|0⟩,|K⟩}`

of two-level `y`-rotations, and the source claims that the first column of `V` in the
computational basis is

`(cos θ_1 ⋯ cos θ_K, cos θ_2 ⋯ cos θ_K sin θ_1, …, cos θ_K sin θ_{K-1}, sin θ_K)`

(Eq. (9)), "which is equivalent to spherical coordinates in `R^{K+1}`", hence
`V : |0⟩ ↦ |ψ⟩` for any `|ψ⟩ ∈ R^{K+1}`.

This module formalizes exactly that chain. The two-level block is written in the
source's Eq. (8) convention, whose first column is `(cos θ, sin θ)`; Eq. (8) writes the
same block as `(t, √(1-t²))` with `t = cos θ`, so the half-angle displayed
`R_y(θ) = [[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]` of Section 2.3 is absorbed by
reparametrization and Eq. (9) is the statement proved here. The source's angles
`θ_1, …, θ_K` are `θ 0, …, θ (K-1)` below.

Main results:

* `prefixProd_col_zero` — the first column after `K` rotations is the Eq. (9) vector,
  i.e. the source's "we claim that the first column of `V` … is the vector (9)";
* `colEntry_sq_sum` — that vector has unit Euclidean norm, i.e. it is a point of the
  unit sphere, the source's "which is equivalent to spherical coordinates in
  `R^{K+1}`";
* `exists_angles` / `exists_angles_prefixProd` — conversely every unit `ψ` in
  `R^{K+1}` with `K ≥ 1` is the first column of such a product, which is the source's
  "thus we have constructed a gate `V : |0⟩ → |ψ⟩` for any `|ψ⟩ ∈ R^{K+1}`";
* `twoLevelRy_mem_unitaryGroup` — each two-level block, hence the product `V` of
  Eq. (9), is a real unitary (orthogonal) matrix; this is the unitarity half of the
  source's `U_ψ` construction that its Eq. (8)--(9) discussion leaves implicit.

The source proves Eq. (9) and reads the unit-norm identity off it; the converse direction
is quoted there without proof, and is where the induction on `K` below does its work (the
last angle is `arcsin ψ_last`, the prefix is renormalized by `cos θ`, and the degenerate
`cos θ = 0` case forces the prefix to vanish).

The source's *cost* accounting (K rotations plus `F (log F)^2` subspace-change logic)
lives in `MainResults/ResourceCount`, not here.

No shared `Qatlib.*` declaration states any of these facts, so no
representation bridge into a frozen interface is asserted here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ViterbiDecode14.MainResults

/-- A finite sum supported on at most the two distinct points `a` and `b` equals the sum of
those two values. This is the counting device used for the two-level rotation's column inner
products. -/
theorem sum_univ_two {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (a b : ι) (hab : a ≠ b) (f : ι → M)
    (hf : ∀ x, x ≠ a → x ≠ b → f x = 0) :
    ∑ x, f x = f a + f b := by
  have hsplit : ∀ x : ι, f x =
      (if x = a then f x else 0) + (if x = b then f x else 0) := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      rw [if_pos rfl, if_neg hab, add_zero]
    · by_cases hxb : x = b
      · subst hxb
        rw [if_neg (Ne.symm hab), if_pos rfl]
        simp
      · rw [if_neg hxa, if_neg hxb, hf x hxa hxb]
        simp
  have hsplitSum : ∑ x : ι, f x =
      (∑ x : ι, if x = a then f x else 0) +
        (∑ x : ι, if x = b then f x else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hsplit x
  rw [hsplitSum]
  simp

/-- The paper-level two-level `y`-rotation `R_y(θ)_{|0⟩,|j+1⟩}` on `R^{K+1}`: it acts as
the source's Eq. (8) block `[[cos θ, -sin θ], [sin θ, cos θ]]` on `span{e_0, e_{j+1}}`
and as the identity on the orthogonal complement. `j` is the zero-based rotation index,
so the source's `R_y(θ_j)_{|0⟩,|j⟩}` is `twoLevelRy K (θ (j-1)) (j-1)`; no bound on `j`
is imposed because the theorem layer always passes `j < K`. -/
def twoLevelRy (K : ℕ) (θ : ℝ) (j : ℕ) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ :=
  fun r c =>
    if r.val = 0 then
      (if c.val = 0 then Real.cos θ
        else if c.val = j + 1 then -Real.sin θ else 0)
    else if r.val = j + 1 then
      (if c.val = 0 then Real.sin θ
        else if c.val = j + 1 then Real.cos θ else 0)
    else if r.val = c.val then 1 else 0

/-- The source's partial product `∏_{j<k} R_y(θ_j)_{|0⟩,|j+1⟩}` on `R^{K+1}`; the `V`
of Eq. (9) is `prefixProd K θ K`. -/
def prefixProd (K : ℕ) (θ : ℕ → ℝ) : ℕ → Matrix (Fin (K+1)) (Fin (K+1)) ℝ
  | 0 => 1
  | k + 1 => prefixProd K θ k * twoLevelRy K (θ k) k

/-- The `i`-th entry of the source's Eq. (9) vector after `k` rotations:
`(∏_{j=i}^{k-1} cos θ_j) · sin θ_{i-1}` for `1 ≤ i ≤ k`, the full product
`∏_{j<k} cos θ_j` for `i = 0`, and `0` beyond `k`. -/
def colEntry (K k : ℕ) (θ : ℕ → ℝ) (i : Fin (K+1)) : ℝ :=
  if i.val ≤ k then
    (∏ j ∈ Finset.Ico i.val k, Real.cos (θ j)) *
      (if i.val = 0 then 1 else Real.sin (θ (i.val - 1)))
  else 0

/-- The two-level block is the identity off the rotated pair `{0, j+1}`. -/
theorem twoLevelRy_eq_ite (K : ℕ) (θ : ℝ) (j : ℕ) (r c : Fin (K+1))
    (hc0 : c.val ≠ 0) (hcj : c.val ≠ j + 1) :
    twoLevelRy K θ j r c = if r = c then 1 else 0 := by
  unfold twoLevelRy
  by_cases h0 : r.val = 0
  · have hrc : r ≠ c := fun h => hc0 (h ▸ h0)
    simp [h0, hc0, hcj, hrc]
  · by_cases hj : r.val = j + 1
    · have hrc : r ≠ c := fun h => hcj (h ▸ hj)
      simp [hj, hc0, hcj, hrc]
    · have hiff : r = c ↔ r.val = c.val := Fin.ext_iff
      simp [h0, hj, hiff]

/-- First-column form of the two-level block: the `|0⟩` column is `(cos θ, sin θ)` on
the slots `{0, j+1}` and zero elsewhere. -/
theorem twoLevelRy_col_zero (K : ℕ) (θ : ℝ) (j : ℕ) (r : Fin (K+1)) :
    twoLevelRy K θ j r 0 =
      if r.val = 0 then Real.cos θ else if r.val = j + 1 then Real.sin θ else 0 := by
  unfold twoLevelRy
  by_cases h0 : r.val = 0
  · simp [h0]
  · by_cases hj : r.val = j + 1
    · simp [hj]
    · simp [h0, hj]

/-- The rotated-pair column of the two-level block: the `|j+1⟩` column is
`(-sin θ, cos θ)` on the slots `{0, j+1}` and zero elsewhere, the second column of
the `[[cos θ, -sin θ], [sin θ, cos θ]]` block of Eq. (8). -/
theorem twoLevelRy_col_rotated (K : ℕ) (θ : ℝ) {j : ℕ} (hj : j < K)
    (r : Fin (K+1)) :
    twoLevelRy K θ j r (⟨j + 1, by omega⟩ : Fin (K+1)) =
      if r.val = 0 then -Real.sin θ else if r.val = j + 1 then Real.cos θ else 0 := by
  unfold twoLevelRy
  by_cases h0 : r.val = 0
  · simp [h0]
  · by_cases hr : r.val = j + 1
    · simp [hr]
    · simp [h0, hr]

/-- Off-pair rows of the two-level block: a row outside `{0, j+1}` is the standard
basis row, so the block acts as the identity on the orthogonal complement of the
rotated plane. -/
theorem twoLevelRy_row_off (K : ℕ) (θ : ℝ) (j : ℕ) (r c : Fin (K+1))
    (hr0 : r.val ≠ 0) (hrj : r.val ≠ j + 1) :
    twoLevelRy K θ j r c = if r = c then 1 else 0 := by
  unfold twoLevelRy
  rw [if_neg hr0, if_neg hrj]
  by_cases h : r = c
  · subst h
    simp
  · have hne : r.val ≠ c.val := fun hh => h (Fin.ext hh)
    simp [h, hne]

/-- For a legal rotation index `j < K`, the two-level `y`-rotation is a real unitary
(orthogonal) matrix. This supplies the unitarity part of the source's `U_ψ` construction;
the cost of implementing the subspace change is accounted separately. -/
theorem twoLevelRy_mem_unitaryGroup (K : ℕ) (θ : ℝ) {j : ℕ} (hj : j < K) :
    twoLevelRy K θ j ∈ Matrix.unitaryGroup (Fin (K+1)) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext r c
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.one_apply]
  have hx0 : (0 : Fin (K+1)) ≠ (⟨j + 1, by omega⟩ : Fin (K+1)) := by simp
  have hx0' : (⟨j + 1, by omega⟩ : Fin (K+1)) ≠ (0 : Fin (K+1)) := Ne.symm hx0
  have hcol0 : ∀ m : Fin (K+1),
      twoLevelRy K θ j m (0 : Fin (K+1)) =
        if m = (0 : Fin (K+1)) then Real.cos θ
        else if m = (⟨j + 1, by omega⟩ : Fin (K+1)) then Real.sin θ else 0 := by
    intro m
    rw [twoLevelRy_col_zero]
    by_cases hm0 : m.val = 0
    · simp [Fin.ext_iff, hm0]
    · by_cases hmx : m.val = j + 1
      · have hmxe : m = (⟨j + 1, by omega⟩ : Fin (K+1)) := by
          simp [Fin.ext_iff, hmx]
        simp [Fin.ext_iff, hmxe]
      · simp [Fin.ext_iff, hm0, hmx]
  have hcolx : ∀ m : Fin (K+1),
      twoLevelRy K θ j m (⟨j + 1, by omega⟩ : Fin (K+1)) =
        if m = (0 : Fin (K+1)) then -Real.sin θ
        else if m = (⟨j + 1, by omega⟩ : Fin (K+1)) then Real.cos θ else 0 := by
    intro m
    rw [twoLevelRy_col_rotated K θ hj m]
    by_cases hm0 : m.val = 0
    · simp [Fin.ext_iff, hm0]
    · by_cases hmx : m.val = j + 1
      · have hmxe : m = (⟨j + 1, by omega⟩ : Fin (K+1)) := by
          simp [Fin.ext_iff, hmx]
        simp [Fin.ext_iff, hmxe]
      · simp [Fin.ext_iff, hm0, hmx]
  by_cases hr0 : r = (0 : Fin (K+1))
  · subst hr0
    have hf0 : ∀ m : Fin (K+1), m ≠ (0 : Fin (K+1)) →
        m ≠ (⟨j + 1, by omega⟩ : Fin (K+1)) →
        twoLevelRy K θ j m (0 : Fin (K+1)) * twoLevelRy K θ j m c = 0 := by
      intro m hm0 hmx
      rw [hcol0 m, if_neg hm0, if_neg hmx, zero_mul]
    have hsum : ∑ m : Fin (K+1),
        twoLevelRy K θ j m (0 : Fin (K+1)) * twoLevelRy K θ j m c =
        twoLevelRy K θ j (0 : Fin (K+1)) (0 : Fin (K+1)) *
            twoLevelRy K θ j (0 : Fin (K+1)) c +
        twoLevelRy K θ j (⟨j + 1, by omega⟩ : Fin (K+1)) (0 : Fin (K+1)) *
            twoLevelRy K θ j (⟨j + 1, by omega⟩ : Fin (K+1)) c :=
      sum_univ_two (0 : Fin (K+1)) (⟨j + 1, by omega⟩ : Fin (K+1)) hx0
        (fun m => twoLevelRy K θ j m (0 : Fin (K+1)) * twoLevelRy K θ j m c) hf0
    rw [hsum]
    by_cases hc0 : c = (0 : Fin (K+1))
    · subst hc0
      rw [hcol0 (0 : Fin (K+1)), hcol0 (⟨j + 1, by omega⟩ : Fin (K+1))]
      simp [hx0']
      linear_combination Real.cos_sq_add_sin_sq θ
    · by_cases hcx : c = (⟨j + 1, by omega⟩ : Fin (K+1))
      · subst hcx
        rw [hcol0 (0 : Fin (K+1)), hcol0 (⟨j + 1, by omega⟩ : Fin (K+1)),
          hcolx (0 : Fin (K+1)), hcolx (⟨j + 1, by omega⟩ : Fin (K+1))]
        simp [hx0, hx0']
        ring
      · have hval0 : c.val ≠ 0 := fun h => hc0 (by simp [Fin.ext_iff, h])
        have hvalx : c.val ≠ j + 1 := fun h => hcx (by simp [Fin.ext_iff, h])
        have hAc : ∀ m : Fin (K+1),
            twoLevelRy K θ j m c = if m = c then 1 else 0 :=
          fun m => twoLevelRy_eq_ite K θ j m c hval0 hvalx
        rw [hcol0 (0 : Fin (K+1)), hcol0 (⟨j + 1, by omega⟩ : Fin (K+1)),
          hAc (0 : Fin (K+1)), hAc (⟨j + 1, by omega⟩ : Fin (K+1))]
        simp [hx0', Ne.symm hc0, Ne.symm hcx]
  · by_cases hrx : r = (⟨j + 1, by omega⟩ : Fin (K+1))
    · subst hrx
      have hfx : ∀ m : Fin (K+1), m ≠ (0 : Fin (K+1)) →
          m ≠ (⟨j + 1, by omega⟩ : Fin (K+1)) →
          twoLevelRy K θ j m (⟨j + 1, by omega⟩ : Fin (K+1)) *
              twoLevelRy K θ j m c = 0 := by
        intro m hm0 hmx
        rw [hcolx m, if_neg hm0, if_neg hmx, zero_mul]
      have hsum : ∑ m : Fin (K+1),
          twoLevelRy K θ j m (⟨j + 1, by omega⟩ : Fin (K+1)) *
              twoLevelRy K θ j m c =
          twoLevelRy K θ j (0 : Fin (K+1)) (⟨j + 1, by omega⟩ : Fin (K+1)) *
              twoLevelRy K θ j (0 : Fin (K+1)) c +
          twoLevelRy K θ j (⟨j + 1, by omega⟩ : Fin (K+1))
              (⟨j + 1, by omega⟩ : Fin (K+1)) *
              twoLevelRy K θ j (⟨j + 1, by omega⟩ : Fin (K+1)) c :=
        sum_univ_two (0 : Fin (K+1)) (⟨j + 1, by omega⟩ : Fin (K+1)) hx0
          (fun m => twoLevelRy K θ j m (⟨j + 1, by omega⟩ : Fin (K+1)) *
            twoLevelRy K θ j m c) hfx
      rw [hsum]
      by_cases hc0 : c = (0 : Fin (K+1))
      · subst hc0
        rw [hcolx (0 : Fin (K+1)), hcolx (⟨j + 1, by omega⟩ : Fin (K+1)),
          hcol0 (0 : Fin (K+1)), hcol0 (⟨j + 1, by omega⟩ : Fin (K+1))]
        simp [hx0']
        ring
      · by_cases hcx : c = (⟨j + 1, by omega⟩ : Fin (K+1))
        · subst hcx
          rw [hcolx (0 : Fin (K+1)), hcolx (⟨j + 1, by omega⟩ : Fin (K+1))]
          simp [hx0']
          linear_combination Real.cos_sq_add_sin_sq θ
        · have hval0 : c.val ≠ 0 := fun h => hc0 (by simp [Fin.ext_iff, h])
          have hvalx : c.val ≠ j + 1 := fun h => hcx (by simp [Fin.ext_iff, h])
          have hAc : ∀ m : Fin (K+1),
              twoLevelRy K θ j m c = if m = c then 1 else 0 :=
            fun m => twoLevelRy_eq_ite K θ j m c hval0 hvalx
          rw [hcolx (0 : Fin (K+1)), hcolx (⟨j + 1, by omega⟩ : Fin (K+1)),
            hAc (0 : Fin (K+1)), hAc (⟨j + 1, by omega⟩ : Fin (K+1))]
          simp [hx0', Ne.symm hc0, Ne.symm hcx]
    · have hrval0 : r.val ≠ 0 := fun h => hr0 (by simp [Fin.ext_iff, h])
      have hrvalx : r.val ≠ j + 1 := fun h => hrx (by simp [Fin.ext_iff, h])
      have hAr : ∀ m : Fin (K+1),
          twoLevelRy K θ j m r = if m = r then 1 else 0 :=
        fun m => twoLevelRy_eq_ite K θ j m r hrval0 hrvalx
      simp only [hAr, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      exact twoLevelRy_row_off K θ j r c hrval0 hrvalx

/-- A column strictly beyond the rotations already applied is untouched: this is the
invariant behind the source's observation that each new rotation only repaints the
`|0⟩` slot and the freshly reached slot `|k+1⟩`. -/
theorem prefixProd_col_fresh (K : ℕ) (θ : ℕ → ℝ) :
    ∀ k (c : Fin (K+1)), k + 1 ≤ c.val → ∀ i : Fin (K+1),
      prefixProd K θ k i c = if i = c then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro c _ i
    simp only [prefixProd, Matrix.one_apply]
  | succ k ih =>
    intro c hc i
    have hc0 : c.val ≠ 0 := by omega
    have hcj : c.val ≠ k + 1 := by omega
    have hstep : prefixProd K θ (k + 1) =
        prefixProd K θ k * twoLevelRy K (θ k) k := rfl
    rw [hstep, Matrix.mul_apply]
    have hterm : ∀ m : Fin (K+1),
        prefixProd K θ k i m * twoLevelRy K (θ k) k m c =
          if m = c then prefixProd K θ k i c else 0 := by
      intro m
      rw [twoLevelRy_eq_ite K (θ k) k m c hc0 hcj]
      by_cases hm : m = c <;> simp [hm]
    rw [Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    exact ih c (by omega) i

/-- The Eq. (9) entries vanish beyond the rotations already applied. -/
theorem colEntry_eq_zero_of_lt (K k : ℕ) (θ : ℕ → ℝ) (i : Fin (K+1))
    (h : k < i.val) : colEntry K k θ i = 0 := by
  unfold colEntry
  rw [if_neg (by omega)]

/-- One more rotation appends the new slot `|k+1⟩` and scales the old column by
`cos θ_k`, exactly the recursion the source reads off the block form of the product. -/
theorem colEntry_succ (K k : ℕ) (θ : ℕ → ℝ) (i : Fin (K+1)) :
    colEntry K (k + 1) θ i = colEntry K k θ i * Real.cos (θ k) +
      (if i.val = k + 1 then Real.sin (θ k) else 0) := by
  unfold colEntry
  by_cases hle : i.val ≤ k
  · have hle' : i.val ≤ k + 1 := by omega
    have hne : i.val ≠ k + 1 := by omega
    have hprod : ∏ j ∈ Finset.Ico i.val (k + 1), Real.cos (θ j) =
        (∏ j ∈ Finset.Ico i.val k, Real.cos (θ j)) * Real.cos (θ k) :=
      Finset.prod_Ico_succ_top hle _
    rw [if_pos hle', if_pos hle, if_neg hne, hprod]
    ring
  · by_cases heq : i.val = k + 1
    · have hle' : i.val ≤ k + 1 := by omega
      have hprod : ∏ j ∈ Finset.Ico i.val (k + 1), Real.cos (θ j) = 1 := by
        rw [Finset.Ico_eq_empty_of_le (by omega : k + 1 ≤ i.val)]
        simp
      have hsin : (if i.val = 0 then (1 : ℝ) else Real.sin (θ (i.val - 1))) =
          Real.sin (θ k) := by
        have hne0 : i.val ≠ 0 := by omega
        rw [if_neg hne0, show i.val - 1 = k from by omega]
      rw [if_pos hle', if_neg hle, if_pos heq, hprod, hsin]
      ring
    · have hnot : ¬ i.val ≤ k + 1 := by omega
      rw [if_neg hnot, if_neg hle, if_neg heq]
      ring

/-- Eq. (9): the first column of `V = ∏_{j<K} R_y(θ_j)_{|0⟩,|j+1⟩}` is the source's
spherical-coordinate vector. -/
theorem prefixProd_col_zero (K : ℕ) (θ : ℕ → ℝ) :
    ∀ k, k ≤ K → ∀ i : Fin (K+1), prefixProd K θ k i 0 = colEntry K k θ i := by
  intro k
  induction k with
  | zero =>
    intro _ i
    rw [prefixProd, Matrix.one_apply]
    by_cases h : i = 0
    · subst h
      simp [colEntry]
    · have hpos : 0 < i.val := by
        rcases Nat.eq_zero_or_pos i.val with h0 | h0
        · exact absurd (Fin.ext h0) h
        · exact h0
      have hle : ¬ i.val ≤ 0 := by omega
      simp [colEntry, h, hle]
  | succ k ih =>
    intro hk i
    have hstep : prefixProd K θ (k + 1) =
        prefixProd K θ k * twoLevelRy K (θ k) k := rfl
    rw [hstep, Matrix.mul_apply]
    have hsplit : ∀ m : Fin (K+1),
        prefixProd K θ k i m * twoLevelRy K (θ k) k m 0 =
          (if m.val = 0 then prefixProd K θ k i m * Real.cos (θ k) else 0) +
            (if m.val = k + 1 then prefixProd K θ k i m * Real.sin (θ k) else 0) := by
      intro m
      rw [twoLevelRy_col_zero]
      by_cases h0 : m.val = 0
      · have hne : m.val ≠ k + 1 := by omega
        rw [if_pos h0, if_pos h0, if_neg hne]
        ring
      · by_cases h1 : m.val = k + 1
        · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1]
          ring
        · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
          ring
    rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
    have hS1 : (∑ m : Fin (K+1),
        (if m.val = 0 then prefixProd K θ k i m * Real.cos (θ k) else 0)) =
        prefixProd K θ k i 0 * Real.cos (θ k) := by
      rw [Finset.sum_eq_single (0 : Fin (K+1))]
      · simp
      · intro b _ hb
        have hb0 : b.val ≠ 0 := fun h => hb (Fin.ext (by simpa using h))
        rw [if_neg hb0]
      · intro h
        simp at h
    have hS2 : (∑ m : Fin (K+1),
        (if m.val = k + 1 then prefixProd K θ k i m * Real.sin (θ k) else 0)) =
        (if i = (⟨k + 1, by omega⟩ : Fin (K+1)) then 1 else 0) * Real.sin (θ k) := by
      rw [Finset.sum_eq_single (⟨k + 1, by omega⟩ : Fin (K+1))]
      · rw [if_pos rfl,
          prefixProd_col_fresh K θ k ⟨k + 1, by omega⟩ (by simp) i]
      · intro b _ hb
        have hbne : b.val ≠ k + 1 := fun h => hb (Fin.ext h)
        rw [if_neg hbne]
      · intro h
        simp at h
    rw [hS1, hS2, colEntry_succ, ih (by omega)]
    by_cases hi : i.val = k + 1
    · have hie : i = (⟨k + 1, by omega⟩ : Fin (K+1)) := Fin.ext hi
      rw [if_pos hi, if_pos hie, colEntry_eq_zero_of_lt K k θ i (by omega)]
      ring
    · have hie : i ≠ (⟨k + 1, by omega⟩ : Fin (K+1)) := fun h => hi (by rw [h])
      rw [if_neg hi, if_neg hie]
      ring

/-- The Eq. (9) vector has unit Euclidean norm: it is a point of the unit sphere of
`R^{K+1}`, i.e. the source's "equivalent to spherical coordinates in `R^{K+1}`". -/
theorem colEntry_sq_sum (K : ℕ) (θ : ℕ → ℝ) :
    ∀ k, k ≤ K → (∑ i : Fin (K+1), (colEntry K k θ i) ^ 2) = 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Finset.sum_eq_single (0 : Fin (K+1))]
    · simp [colEntry]
    · intro b _ hb
      have hpos : 0 < b.val := by
        rcases Nat.eq_zero_or_pos b.val with h0 | h0
        · exact absurd (Fin.ext h0) hb
        · exact h0
      rw [colEntry, if_neg (by omega)]
      ring
    · intro h
      simp at h
  | succ k ih =>
    intro hk
    have hterm : ∀ i : Fin (K+1), (colEntry K (k + 1) θ i) ^ 2 =
        (Real.cos (θ k)) ^ 2 * (colEntry K k θ i) ^ 2 +
          2 * (colEntry K k θ i * Real.cos (θ k)) *
            (if i.val = k + 1 then Real.sin (θ k) else 0) +
          (if i.val = k + 1 then Real.sin (θ k) else 0) ^ 2 := by
      intro i
      rw [colEntry_succ]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    have hsq : (∑ i : Fin (K+1),
        (Real.cos (θ k)) ^ 2 * (colEntry K k θ i) ^ 2) = (Real.cos (θ k)) ^ 2 := by
      rw [← Finset.mul_sum, ih (by omega), mul_one]
    have hcross : (∑ i : Fin (K+1),
        2 * (colEntry K k θ i * Real.cos (θ k)) *
          (if i.val = k + 1 then Real.sin (θ k) else 0)) = 0 := by
      rw [Finset.sum_eq_single (⟨k + 1, by omega⟩ : Fin (K+1))]
      · rw [if_pos rfl, colEntry_eq_zero_of_lt K k θ (⟨k + 1, by omega⟩) (by simp)]
        ring
      · intro b _ hb
        have hbne : b.val ≠ k + 1 := fun h => hb (Fin.ext h)
        rw [if_neg hbne]
        ring
      · intro h
        simp at h
    have hdelta : (∑ i : Fin (K+1),
        (if i.val = k + 1 then Real.sin (θ k) else 0) ^ 2) =
        (Real.sin (θ k)) ^ 2 := by
      rw [Finset.sum_eq_single (⟨k + 1, by omega⟩ : Fin (K+1))]
      · rw [if_pos rfl]
      · intro b _ hb
        have hbne : b.val ≠ k + 1 := fun h => hb (Fin.ext h)
        rw [if_neg hbne]
        ring
      · intro h
        simp at h
    rw [hsq, hcross, hdelta]
    linarith [Real.cos_sq_add_sin_sq (θ k)]

/-- `colEntry` depends only on the numeric index and on the angles below `k`, so the
same Eq. (9) entry can be read off in any ambient dimension. -/
theorem colEntry_congr (K K' k : ℕ) (θ θ' : ℕ → ℝ) (i : Fin (K+1)) (i' : Fin (K'+1))
    (hval : i.val = i'.val) (hθ : ∀ j, j < k → θ j = θ' j) :
    colEntry K k θ i = colEntry K' k θ' i' := by
  unfold colEntry
  rw [hval]
  by_cases h : i'.val ≤ k
  · rw [if_pos h, if_pos h]
    congr 1
    · exact Finset.prod_congr rfl (fun j hj => by
        rw [hθ j (Finset.mem_Ico.mp hj).2])
    · by_cases h0 : i'.val = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0]
        rw [hθ (i'.val - 1) (by omega)]
  · rw [if_neg h, if_neg h]

/-- The single-rotation column of Eq. (9) is `(cos θ_0, sin θ_0)`: its `|0⟩` entry. -/
theorem colEntry_one_cos (θ : ℕ → ℝ) :
    colEntry 1 1 θ (0 : Fin 2) = Real.cos (θ 0) := by
  rw [colEntry_succ]
  have h0 : colEntry 1 0 θ (0 : Fin 2) = 1 := by
    unfold colEntry
    simp
  rw [h0]
  simp

/-- The single-rotation column of Eq. (9) is `(cos θ_0, sin θ_0)`: its `|1⟩` entry. -/
theorem colEntry_one_sin (θ : ℕ → ℝ) :
    colEntry 1 1 θ (1 : Fin 2) = Real.sin (θ 0) := by
  rw [colEntry_succ]
  have h0 : colEntry 1 0 θ (1 : Fin 2) = 0 := by
    unfold colEntry
    simp
  rw [h0]
  simp

/-- Every unit vector of `R^{K+1}` with `K ≥ 1` is the first column of the source's
canonical product of two-level `y`-rotations: the operative form of the source's
corollary "thus we have constructed a gate `V : |0⟩ → |ψ⟩` for any `|ψ⟩ ∈ R^{K+1}`". -/
theorem exists_angles : ∀ K : ℕ, 1 ≤ K → ∀ ψ : Fin (K+1) → ℝ,
    (∑ i : Fin (K+1), ψ i ^ 2 = 1) → ∃ θ : ℕ → ℝ, ∀ i, colEntry K K θ i = ψ i := by
  intro K
  induction K with
  | zero => intro h; omega
  | succ n ih =>
    intro _hn ψ hψ
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- one rotation, dimension two
      subst hn0
      change ∃ θ : ℕ → ℝ, ∀ i : Fin 2, colEntry 1 1 θ i = ψ i
      have hsum : ψ 0 ^ 2 + ψ 1 ^ 2 = 1 := by
        simpa [Fin.sum_univ_two] using hψ
      have hb1 : -1 ≤ ψ 1 := by nlinarith [sq_abs (ψ 1), sq_nonneg (ψ 0)]
      have hb2 : ψ 1 ≤ 1 := by nlinarith [sq_abs (ψ 1), sq_nonneg (ψ 0)]
      have hsq : (1 : ℝ) - ψ 1 ^ 2 = ψ 0 ^ 2 := by linarith
      by_cases hsign : 0 ≤ ψ 0
      · refine ⟨fun _ => Real.arcsin (ψ 1), ?_⟩
        have hsin : Real.sin (Real.arcsin (ψ 1)) = ψ 1 := Real.sin_arcsin hb1 hb2
        have hcos : Real.cos (Real.arcsin (ψ 1)) = ψ 0 := by
          rw [Real.cos_arcsin, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsign]
        intro i
        fin_cases i
        · show colEntry 1 1 _ (0 : Fin 2) = ψ 0
          rw [colEntry_one_cos, hcos]
        · show colEntry 1 1 _ (1 : Fin 2) = ψ 1
          rw [colEntry_one_sin, hsin]
      · have hsign' : ψ 0 < 0 := lt_of_not_ge hsign
        refine ⟨fun _ => Real.pi - Real.arcsin (ψ 1), ?_⟩
        have hsin : Real.sin (Real.pi - Real.arcsin (ψ 1)) = ψ 1 := by
          rw [Real.sin_pi_sub, Real.sin_arcsin hb1 hb2]
        have hcos : Real.cos (Real.pi - Real.arcsin (ψ 1)) = ψ 0 := by
          rw [Real.cos_pi_sub, Real.cos_arcsin, hsq, Real.sqrt_sq_eq_abs,
            abs_of_neg hsign']
          ring
        intro i
        fin_cases i
        · show colEntry 1 1 _ (0 : Fin 2) = ψ 0
          rw [colEntry_one_cos, hcos]
        · show colEntry 1 1 _ (1 : Fin 2) = ψ 1
          rw [colEntry_one_sin, hsin]
    · -- at least two rotations
      change ∃ θ : ℕ → ℝ, ∀ i : Fin (n + 2), colEntry (n+1) (n+1) θ i = ψ i
      have hsplit : (∑ i : Fin (n+1), ψ (Fin.castSucc i) ^ 2) +
          ψ (Fin.last (n+1)) ^ 2 = 1 := by
        rw [← Fin.sum_univ_castSucc (fun i : Fin ((n+1)+1) => ψ i ^ 2)]
        exact hψ
      have hb1 : -1 ≤ ψ (Fin.last (n+1)) := by
        nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
          sq_nonneg (ψ (Fin.castSucc i)))]
      have hb2 : ψ (Fin.last (n+1)) ≤ 1 := by
        nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
          sq_nonneg (ψ (Fin.castSucc i)))]
      set t : ℝ := Real.arcsin (ψ (Fin.last (n+1))) with ht
      have hsin : Real.sin t = ψ (Fin.last (n+1)) := Real.sin_arcsin hb1 hb2
      have hcos_sq : Real.cos t ^ 2 = 1 - ψ (Fin.last (n+1)) ^ 2 := by
        have h := Real.cos_sq_add_sin_sq t
        rw [hsin] at h
        linarith
      by_cases hc0 : Real.cos t = 0
      · -- degenerate prefix: all prefix coordinates vanish
        have hpref : ∀ i : Fin (n+1), ψ (Fin.castSucc i) = 0 := by
          have hz : ∑ i : Fin (n+1), ψ (Fin.castSucc i) ^ 2 = 0 := by
            have hc : Real.cos t ^ 2 = 0 := by rw [hc0]; ring
            linarith
          intro i
          have hterm := (Finset.sum_eq_zero_iff_of_nonneg
            (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ψ (Fin.castSucc j)))).mp hz i
            (Finset.mem_univ i)
          exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hterm
        refine ⟨fun j => if j = n then t else 0, ?_⟩
        intro i
        rw [colEntry_succ]
        simp only [if_true]
        by_cases hi : i.val = n + 1
        · have hie : i = Fin.last (n+1) := Fin.ext hi
          rw [if_pos hi, hie,
            colEntry_eq_zero_of_lt (n+1) n (fun j => if j = n then t else 0)
              (Fin.last (n+1)) (by simp)]
          rw [zero_mul, zero_add]
          exact hsin
        · rw [if_neg hi]
          have hzero : ψ i = 0 := by
            have hcast : (Fin.castSucc (⟨i.val, by omega⟩ : Fin (n+1)) : Fin ((n+1)+1)) = i :=
              Fin.ext rfl
            rw [← hcast]
            exact hpref ⟨i.val, by omega⟩
          rw [hc0, mul_zero, zero_add, hzero]
      · -- general case: normalize the prefix and recurse
        set ψ' : Fin (n+1) → ℝ := fun j => ψ (Fin.castSucc j) / Real.cos t with hψ'def
        have hpref_eq : ∑ j : Fin (n+1), ψ (Fin.castSucc j) ^ 2 = Real.cos t ^ 2 := by
          have hs : ψ (Fin.last (n+1)) ^ 2 = Real.sin t ^ 2 := by rw [← hsin]
          linarith
        have hψ'sum : ∑ j : Fin (n+1), ψ' j ^ 2 = 1 := by
          have hc2 : Real.cos t ^ 2 ≠ 0 := pow_ne_zero 2 hc0
          simp only [hψ'def, div_pow]
          rw [← Finset.sum_div, hpref_eq]
          exact div_self hc2
        obtain ⟨θ', hθ'⟩ := ih hnpos ψ' hψ'sum
        refine ⟨fun j => if j = n then t else θ' j, ?_⟩
        intro i
        rw [colEntry_succ]
        simp only [if_true]
        by_cases hi : i.val = n + 1
        · have hie : i = Fin.last (n+1) := Fin.ext hi
          rw [if_pos hi, hie,
            colEntry_eq_zero_of_lt (n+1) n (fun j => if j = n then t else θ' j)
              (Fin.last (n+1)) (by simp)]
          rw [zero_mul, zero_add]
          exact hsin
        · rw [if_neg hi]
          have hcongr := colEntry_congr (n+1) n n
            (fun j => if j = n then t else θ' j) θ' i ⟨i.val, by omega⟩ rfl
            (fun j hj => by
              have hjn : j ≠ n := by omega
              simp only [hjn, if_false])
          rw [hcongr, hθ' ⟨i.val, by omega⟩]
          show ψ (Fin.castSucc ⟨i.val, by omega⟩) / Real.cos t * Real.cos t + 0 = ψ i
          rw [div_mul_cancel₀ _ hc0, add_zero]
          congr 1

/-- The source's `V : |0⟩ ↦ |ψ⟩` for any desired `|ψ⟩`: every unit vector of `R^{K+1}`
with `K ≥ 1` is the `|0⟩` column of the product `V = ∏_{j<K} R_y(θ_j)_{|0⟩,|j+1⟩}` of
two-level `y`-rotations. -/
theorem exists_angles_prefixProd (K : ℕ) (hK : 1 ≤ K) (ψ : Fin (K+1) → ℝ)
    (hψ : ∑ i : Fin (K+1), ψ i ^ 2 = 1) :
    ∃ θ : ℕ → ℝ, ∀ i : Fin (K+1), prefixProd K θ K i 0 = ψ i := by
  obtain ⟨θ, hθ⟩ := exists_angles K hK ψ hψ
  exact ⟨θ, fun i => by rw [prefixProd_col_zero K θ K le_rfl i, hθ i]⟩

end Qatlib.Papers.ViterbiDecode14.MainResults
