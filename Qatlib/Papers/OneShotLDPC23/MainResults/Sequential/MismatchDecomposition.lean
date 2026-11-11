/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneShotLDPC23.MainResults.Model.BinaryWeight

set_option backward.isDefEq.respectTransparency false

/-!
# OneShotLDPC23.MainResults.Sequential.MismatchDecomposition — Lemmas 4.12 and 4.13

Fixed paper: **arXiv:2306.12470v2**, §4.3, pp. 20–22.

`DeltaDecomposes δ Z F` records a successful run of Algorithm 2 with parameter
`δ`: `F = {x₁, …, x_t}` are the returned local codewords, they sum to `Z`
(Algorithm 2 halts at `Ẑ = 0`), and at every step

  `|Z_{i−1}| − |Z_i| ≥ (1 − δ)|x_i|`,   `Z_i = Z_{i−1} + x_i`.

Lemma 4.12 (`lemma_4_12`) sandwiches `|Z|` between `(1 − δ)Σ|x_i|` and
`Σ|x_i|` by telescoping.  Lemma 4.13 (`lemma_4_13`) is the noisy-mismatch
counting bound `Σ_{x∈F*} |x| ≥ c₁|Z| − c₂|Z_N|` with
`c₁ = (ε − 2δ)/(ε(1−δ))`, `c₂ = 2/ε`, proved via the overlap identity
`|Z̃| − |Z̃ + x| = 2|Z̃ ∩ x| − |x|` and the union bound
`|Z̃ ∩ Σxᵢ| ≤ Σ|Z̃ ∩ xᵢ|`.

Boundary: only the weight combinatorics of §4.3 is formalized; the fact that
Algorithm 2 produces such an `F` (Lemma 4.15) is a separate statement.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Sequential

open Model
open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped BigOperators

/-! ## The decomposition predicate -/

/-- Recursive form of the telescoping condition of Algorithm 2: at every step the
mismatch weight drops by at least `(1 − δ)` times the weight of the added
codeword.  This is exactly `|Z_{i−1}| − |Z_i| ≥ (1 − δ)|x_i|` with
`Z_i = Z_{i−1} + x_i`. -/
def StepReduces {Q : Type*} [Fintype Q] (δ : ℝ) (Z : BitVec Q) :
    List (BitVec Q) → Prop
  | [] => True
  | x :: xs => (1 - δ) * weightR x ≤ weightR Z - weightR (Z + x) ∧
      StepReduces δ (Z + x) xs

/-- Source Definition 4.11 / Algorithm 2 (p. 20): `Z` is `δ`-decomposable with
returned codewords `F = {xᵢ}` when `F` sums to `Z` and every step satisfies the
`δ` reduction condition. -/
def DeltaDecomposes {Q : Type*} [Fintype Q] (δ : ℝ) (Z : BitVec Q)
    (F : List (BitVec Q)) : Prop :=
  Z = F.sum ∧ StepReduces δ Z F

/-- Telescoping: the accumulated `δ`-reduction is at most the total weight drop
from `Z` to `Z + ΣF`. -/
theorem step_reduces_cumulative {Q : Type*} [Fintype Q] (δ : ℝ)
    (F : List (BitVec Q)) (Z : BitVec Q) (h : StepReduces δ Z F) :
    (1 - δ) * (F.map weightR).sum ≤ weightR Z - weightR (Z + F.sum) := by
  induction F generalizing Z with
  | nil => simp [StepReduces]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := h
    have hrest := ih (Z + x) hxs
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    have hassoc : Z + (x + xs.sum) = (Z + x) + xs.sum := by abel
    rw [hassoc]
    have := mul_add (1 - δ) (weightR x) (xs.map weightR).sum
    linarith

/-- **Source Lemma 4.12** (arXiv:2306.12470v2, §4.3 p. 20).
Let `Z` be a `δ`-decomposable mismatch and let `F = {xᵢ}_{i=1}^t` be the
codewords returned by Algorithm 2.  Then

  `(1 − δ) Σᵢ |xᵢ| ≤ |Z| ≤ Σᵢ |xᵢ|`. -/
theorem lemma_4_12 {Q : Type*} [Fintype Q] (δ : ℝ) (Z : BitVec Q)
    (F : List (BitVec Q)) (hdec : DeltaDecomposes δ Z F) :
    (1 - δ) * (F.map weightR).sum ≤ weightR Z ∧ weightR Z ≤ (F.map weightR).sum := by
  obtain ⟨hZ, hstep⟩ := hdec
  constructor
  · have hcum := step_reduces_cumulative δ F Z hstep
    have hsum : Z + F.sum = 0 := by
      rw [← hZ]
      funext i
      exact CharTwo.add_self_eq_zero (Z i)
    rw [hsum, weightR_zero, sub_zero] at hcum
    exact hcum
  · rw [hZ]
    exact weightR_list_sum_le F

/-! ## Overlap identities used in Lemma 4.13 -/

/-- In `F₂`, the sum of two nonzero elements vanishes. -/
theorem binary_add_eq_zero (a b : ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) : a + b = 0 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with h | h
  · exact absurd h ha
  · rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with h' | h'
    · exact absurd h' hb
    · rw [h, h']; decide

/-- Positions where `x` is nonzero and `x + y` is nonzero are exactly those
where `x` is nonzero and `y` vanishes. -/
theorem overlap_add_left_eq {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    overlap (x + y) x = (Finset.univ.filter fun i => x i ≠ 0 ∧ y i = 0).card := by
  unfold overlap
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨hxy, hx⟩
    refine ⟨hx, ?_⟩
    by_contra hy
    exact hxy (binary_add_eq_zero (x i) (y i) hx hy)
  · rintro ⟨hx, hy⟩
    refine ⟨?_, hx⟩
    show x i + y i ≠ 0
    rw [hy, add_zero]
    exact hx

/-- `|(x + y) ∩ x| + |x ∩ y| = |x|`. -/
theorem overlap_add_left_self {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    overlap (x + y) x + overlap x y = bitWeight x := by
  rw [overlap_add_left_eq]
  unfold overlap bitWeight
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hx : x i = 0
  · have h1 : ¬ ((x + y) i ≠ 0 ∧ x i ≠ 0) := fun h => h.2 hx
    have h2 : ¬ (x i ≠ 0 ∧ y i ≠ 0) := fun h => h.1 hx
    simp [hx, h1, h2]
  · by_cases hy : y i = 0
    · have hxy : (x + y) i ≠ 0 := by
        show x i + y i ≠ 0
        rw [hy, add_zero]
        exact hx
      have h2 : ¬ (x i ≠ 0 ∧ y i ≠ 0) := fun h => h.2 hy
      simp [hx, hy, hxy, h2]
    · have hxy : (x + y) i = 0 := binary_add_eq_zero (x i) (y i) hx hy
      simp [hx, hy, hxy]

/-- Real form: `|(x+y) ∩ x| + |x ∩ y| = |x|`. -/
theorem overlapR_add_left_self {Q : Type*} [Fintype Q] (x y : BitVec Q) :
    overlapR (x + y) x + overlapR x y = weightR x := by
  unfold overlapR weightR
  have h := overlap_add_left_self x y
  exact_mod_cast h

/-! ## List-sum bookkeeping -/

/-- Splitting a list sum along a predicate, additively. -/
theorem list_sum_filter_add {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ) :
    ((l.filter p).map f).sum + ((l.filter fun x => !p x).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : p x = true
    · simp [hx] at ih ⊢
      linarith
    · have hx' : p x = false := by
        cases hp : p x
        · rfl
        · exact absurd hp hx
      simp [hx', hx] at ih ⊢
      linarith

/-- Termwise comparison of mapped list sums. -/
theorem list_sum_le_sum {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Casting the natural-valued list sum of overlaps to `ℝ` gives the sum of
`overlapR`. -/
theorem map_overlap_cast {Q : Type*} [Fintype Q] (z : BitVec Q) (l : List (BitVec Q)) :
    ((l.map (overlap z)).sum : ℝ) = (l.map (fun x => overlapR z x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]
    rfl

/-! ## Lemma 4.13 -/

/-- **Source Lemma 4.13** (arXiv:2306.12470v2, §4.3 p. 21, eq. (7)).
Let `Z` be a mismatch vector, `Z_N` any vector, `Z̃ = Z + Z_N`, and suppose `Z`
is `δ`-decomposable with decomposition `F = {xᵢ}`.  For
`F* = {x ∈ F : |Z̃| − |Z̃ + x| ≥ (1 − ε)|x|}`,

  `Σ_{x∈F*} |x| ≥ c₁ |Z| − c₂ |Z_N|`,  `c₁ = (ε − 2δ)/(ε(1−δ))`, `c₂ = 2/ε`.

`ε` is the parameter of Algorithm 2; in the paper `ε ∈ (0,1)` (cf. Theorem 4.1,
"Let ε ∈ (0,1)"), and only `ε < 1` is used.  If `F* = ∅` then
`c₁|Z| ≤ c₂|Z_N|` (the `sum = 0` specialization). -/
theorem lemma_4_13 {Q : Type*} [Fintype Q] [DecidableEq Q]
    (Z ZN : BitVec Q) (F : List (BitVec Q)) (δ ε : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hdec : DeltaDecomposes δ Z F) :
    ((ε - 2 * δ) / (ε * (1 - δ))) * weightR Z - (2 / ε) * weightR ZN ≤
      ((F.filter fun x => (1 - ε) * weightR x ≤
        weightR (Z + ZN) - weightR (Z + ZN + x)).map weightR).sum := by
  classical
  obtain ⟨hZ, hstep⟩ := hdec
  obtain ⟨hlow, hhigh⟩ := lemma_4_12 δ Z F ⟨hZ, hstep⟩
  have hδ1' : 0 < 1 - δ := by linarith
  set Zt : BitVec Q := Z + ZN
  set p : BitVec Q → Bool :=
    fun x => decide ((1 - ε) * weightR x ≤ weightR Zt - weightR (Zt + x))
  set Fs : List (BitVec Q) := F.filter p
  set Fb : List (BitVec Q) := F.filter fun x => !p x
  -- the two filters split `F` additively
  have hFsum : (Fs.map weightR).sum + (Fb.map weightR).sum = (F.map weightR).sum := by
    have h := list_sum_filter_add F p weightR
    simpa [Fs, Fb] using h
  -- single-codeword weight identity
  have hsingle : ∀ x : BitVec Q,
      weightR Zt - weightR (Zt + x) = 2 * overlapR Zt x - weightR x := by
    intro x
    have h := weight_add_exact Zt x
    linarith
  -- (i) upper bound on the total overlap `T = Σ_x |Z̃ ∩ x|`
  have hupper : (F.map (fun x => overlapR Zt x)).sum ≤
      (Fs.map weightR).sum + (1 - ε / 2) * (Fb.map weightR).sum := by
    have hsplit : (F.map (fun x => overlapR Zt x)).sum =
        (Fs.map (fun x => overlapR Zt x)).sum +
          (Fb.map (fun x => overlapR Zt x)).sum := by
      have h := list_sum_filter_add F p (fun x => overlapR Zt x)
      simpa [Fs, Fb] using h.symm
    rw [hsplit]
    have h1 : (Fs.map (fun x => overlapR Zt x)).sum ≤ (Fs.map weightR).sum := by
      refine list_sum_le_sum Fs _ _ ?_
      intro x hx
      rw [List.mem_filter] at hx
      unfold overlapR weightR
      exact_mod_cast overlap_le_right Zt x
    have h2 : (Fb.map (fun x => overlapR Zt x)).sum ≤
        (1 - ε / 2) * (Fb.map weightR).sum := by
      have hb : ∀ x ∈ Fb, overlapR Zt x ≤ (1 - ε / 2) * weightR x := by
        intro x hx
        rw [List.mem_filter] at hx
        have hpx : p x = false := by simpa using hx.2
        have hnot : ¬ ((1 - ε) * weightR x ≤ weightR Zt - weightR (Zt + x)) := by
          simpa [p] using hpx
        have hlt : weightR Zt - weightR (Zt + x) < (1 - ε) * weightR x := not_le.mp hnot
        rw [hsingle x] at hlt
        nlinarith [hlt]
      calc (Fb.map (fun x => overlapR Zt x)).sum
          ≤ (Fb.map (fun x => (1 - ε / 2) * weightR x)).sum := list_sum_le_sum Fb _ _ hb
        _ = (1 - ε / 2) * (Fb.map weightR).sum :=
            List.sum_map_mul_left Fb weightR (1 - ε / 2)
    linarith
  -- (ii) lower bound `T ≥ |Z| − |Z_N|`
  have hlower : weightR Z - weightR ZN ≤ (F.map (fun x => overlapR Zt x)).sum := by
    have h1 : overlapR Zt Z ≤ (F.map (fun x => overlapR Zt x)).sum := by
      have hsum : F.sum = Z := hZ.symm
      calc overlapR Zt Z = overlapR Zt F.sum := by rw [hsum]
        _ = ((overlap Zt F.sum : ℕ) : ℝ) := rfl
        _ ≤ (((F.map (overlap Zt)).sum : ℕ) : ℝ) := by
            exact_mod_cast overlap_list_sum_le Zt F
        _ = (F.map (fun x => overlapR Zt x)).sum := map_overlap_cast Zt F
    have h2 : weightR Z - weightR ZN ≤ overlapR Zt Z := by
      have hid := overlapR_add_left_self Z ZN
      have hle : overlapR Z ZN ≤ weightR ZN := by
        unfold overlapR weightR
        exact_mod_cast overlap_le_right Z ZN
      have hZt : Zt = Z + ZN := rfl
      rw [hZt]
      linarith
    linarith
  -- (iii) combine
  have hmain : weightR Z - weightR ZN ≤
      (ε / 2) * (Fs.map weightR).sum + (2 - ε) / (2 * (1 - δ)) * weightR Z := by
    have h1 : (1 - ε / 2) * (F.map weightR).sum ≤
        (2 - ε) / (2 * (1 - δ)) * weightR Z := by
      have hle' : (F.map weightR).sum ≤ weightR Z / (1 - δ) := by
        rw [le_div_iff₀ hδ1']; linarith
      have hnn : (0 : ℝ) ≤ 1 - ε / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hle' hnn
      have heq : (1 - ε / 2) * (weightR Z / (1 - δ)) =
          (2 - ε) / (2 * (1 - δ)) * weightR Z := by
        field_simp
        try ring
      linarith
    nlinarith [le_trans hlower hupper, hFsum, h1]
  have hkey : (2 / ε) * (weightR Z - weightR ZN - (2 - ε) / (2 * (1 - δ)) * weightR Z) =
      (ε - 2 * δ) / (ε * (1 - δ)) * weightR Z - (2 / ε) * weightR ZN := by
    field_simp
    ring
  have hmid : weightR Z - weightR ZN - (2 - ε) / (2 * (1 - δ)) * weightR Z ≤
      (ε / 2) * (Fs.map weightR).sum := by linarith [hmain]
  have hscale := mul_le_mul_of_nonneg_left hmid
    (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) hε))
  have hcollapse : (2 / ε) * ((ε / 2) * (Fs.map weightR).sum) = (Fs.map weightR).sum := by
    field_simp
  rw [hkey, hcollapse] at hscale
  simpa [Fs, p, Zt] using hscale

end Qatlib.Papers.OneShotLDPC23.MainResults.Sequential
