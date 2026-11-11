/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Qatlib.Papers.ProbStructure26.StatePrep.LocalUpdate
import Qatlib.Papers.ProbStructure26.StatePrep.ResourceLedger

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Fixed Hamming weight (Dicke) blocks

Formal core of Supplementary Section III.1 (Eq. (S19)–(S22)) of *Harnessing
problem structure for end-to-end quantum state preparation*
(arXiv:2609.40105v1).

A block of length `m` with residual Hamming weight `r` has the right-packed
representative `c_{m,r} = 0^{m-r} 1^r`.  Splitting it into children of lengths
`mL` and `mR`, the interface label is the weight `q` of the left child, the
representative of label `q` is `c_{mL,q} ⊔ c_{mR,r-q}`, and the uniform split
mass is the binomial count `M_q = C(mL,q) C(mR,r-q)`.

The declarations below prove the mathematical ingredients of Lemma S2 and
Corollary S2:

* **Vandermonde mass identity.** `∑_q M_q = C(mL+mR, r)`
  (`sum_splitMass`), so the split masses are the child feasible-set sizes and
  sum to the size of the block feasible set.
* **Two-bit support.** Neighbouring labels `q` and `q+1` differ in exactly two
  sites, with pattern `(0,1)` and `(1,0)` (`neighbor_support_card`,
  `neighbor_pattern`).
* **Constant controls.** The neighbouring-boundary conditions number at most
  four (`neighbor_control_card`).
* **Resources.** The layer sums of Eq. (S21) and (S22) are bounded by
  `k log(n/k)` and `n k` through geometric series (`dicke_depth_le`,
  `dicke_gate_le`).
-/

namespace Qatlib.Papers.ProbStructure26.StatePrep

open Finset

/-- The Hamming weight of a bit string. -/
def weight {n : ℕ} (x : BitString n) : ℕ := ∑ i, (x i).toNat

/-- The right-packed representative of a length-`m` block with `r` ones: the
sites `m-r, …, m-1` carry `1` and all earlier sites carry `0` (Eq. (S19)). -/
def packed (m r : ℕ) (i : Fin m) : Bool := decide (m - r ≤ i.val)

/-- `packed m r` has a one exactly at the packed positions. -/
theorem packed_apply (m r : ℕ) (i : Fin m) :
    packed m r i = true ↔ m - r ≤ i.val := by
  simp [packed]

/-- The packed positions of a length-`m` block number exactly `r`. -/
theorem card_packed_positions (m r : ℕ) (hr : r ≤ m) :
    (Finset.univ.filter (fun i : Fin m => m - r ≤ i.val)).card = r := by
  have hbij := Finset.card_bij (s := Finset.univ.filter (fun i : Fin m => m - r ≤ i.val))
    (t := Finset.range r) (fun i _ => i.val - (m - r)) ?_ ?_ ?_
  · simpa using hbij
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_range]
    omega
  · intro i1 hi1 i2 hi2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    apply Fin.ext
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨⟨m - r + k, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · simp

/-- The right-packed representative has weight `r`. -/
theorem weight_packed (m r : ℕ) (hr : r ≤ m) : weight (packed m r) = r := by
  unfold weight
  have hto : (∑ i : Fin m, (packed m r i).toNat) =
      ∑ i : Fin m, (if m - r ≤ i.val then (1 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : m - r ≤ i.val
    · simp [packed, h]
    · simp [packed, h]
  rw [hto]
  have hct : ((Finset.univ.filter (fun i : Fin m => m - r ≤ i.val)).card : ℕ) =
      ∑ i : Fin m, (if m - r ≤ i.val then (1 : ℕ) else 0) := by
    rw [Finset.sum_boole, Nat.cast_id]
  rw [← hct]
  exact card_packed_positions m r hr

/-- Concatenation of a left block of length `mL` and a right block of length
`mR`. -/
def concat {mL mR : ℕ} (x : BitString mL) (y : BitString mR) : BitString (mL + mR) :=
  fun i => if h : (i : ℕ) < mL then x ⟨i, h⟩ else y ⟨i - mL, by have := i.isLt; omega⟩

/-- Concatenation restricts to the left block on its first `mL` positions. -/
theorem concat_left {mL mR : ℕ} (x : BitString mL) (y : BitString mR) (i : Fin mL) :
    concat x y ⟨i.val, by omega⟩ = x i := by
  simp [concat, i.isLt]

/-- Concatenation restricts to the right block on its last `mR` positions. -/
theorem concat_right {mL mR : ℕ} (x : BitString mL) (y : BitString mR) (j : Fin mR) :
    concat x y ⟨mL + j.val, by omega⟩ = y j := by
  simp only [concat]
  rw [dif_neg (by omega)]
  have hfin : (⟨mL + j.val - mL, by omega⟩ : Fin mR) = j := by
    apply Fin.ext
    simp
  rw [hfin]

/-- The weight of a concatenation is the sum of the child weights. -/
theorem weight_concat {mL mR : ℕ} (x : BitString mL) (y : BitString mR) :
    weight (concat x y) = weight x + weight y := by
  unfold weight
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have h : concat x y (Fin.castAdd mR i) = x i := by
      unfold concat Fin.castAdd Fin.castLE
      rw [dif_pos i.isLt]
    rw [h]
  · apply Finset.sum_congr rfl
    intro j _
    have h : concat x y (Fin.natAdd mL j) = y j := by
      unfold concat
      simp only [Fin.natAdd]
      rw [dif_neg (by omega)]
      congr 1
      apply Fin.ext
      simp
    rw [h]

/-- The representative of interface label `q` in a block with children of
length `mL, mR`: `c_{m,r}^{(q)} = c_{mL,q} ⊔ c_{mR,r-q}` (Eq. (S19)). -/
def labelRep (mL mR r q : ℕ) : BitString (mL + mR) :=
  concat (packed mL q) (packed mR (r - q))

/-- Each label representative has weight `r`, so every interface label really
lies in the residual weight-`r` block. -/
theorem weight_labelRep {mL mR r q : ℕ} (hqL : q ≤ mL) (hqR : r - q ≤ mR)
    (hq : q ≤ r) :
    weight (labelRep mL mR r q) = r := by
  unfold labelRep
  rw [weight_concat, weight_packed mL q hqL, weight_packed mR (r - q) hqR]
  omega

/-- The uniform split mass routed through label `q`: the product of the child
binomial counts `M_q = C(mL,q) C(mR,r-q)` (Eq. (S19)). -/
def splitMass (mL mR r q : ℕ) : ℕ := mL.choose q * mR.choose (r - q)

/-- Vandermonde: the split masses over all labels sum to the size `C(mL+mR,r)`
of the block's feasible set (Eq. (S11)–(S12)). -/
theorem sum_splitMass (mL mR r : ℕ) :
    (∑ q ∈ Finset.range (r + 1), splitMass mL mR r q) = (mL + mR).choose r := by
  unfold splitMass
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Left changing site of the neighbouring-label update. -/
def leftSite (mL q : ℕ) : ℕ := mL - q - 1

/-- Right changing site of the neighbouring-label update. -/
def rightSite (mL mR r q : ℕ) : ℕ := mL + (mR - (r - q))

/-- The neighbouring-boundary control set: the two sites adjacent to each
changing site (positions outside the register are omitted by construction). -/
def neighborControls (mL mR r q : ℕ) : Finset (Fin (mL + mR)) :=
  Finset.univ.filter (fun i : Fin (mL + mR) =>
    i.val + 1 = leftSite mL q ∨ i.val = leftSite mL q + 1 ∨
    i.val + 1 = rightSite mL mR r q ∨ i.val = rightSite mL mR r q + 1)

/-- Sites not at the two changing positions keep the same bit in labels `q` and
`q+1`. -/
theorem labelRep_neighbor_agree {mL mR r q : ℕ} (hq : q < mL) (hrq : q < r)
    {i : Fin (mL + mR)}
    (h1 : i.val ≠ leftSite mL q) (h2 : i.val ≠ rightSite mL mR r q) :
    labelRep mL mR r q i = labelRep mL mR r (q + 1) i := by
  unfold labelRep concat packed leftSite rightSite at *
  by_cases hlt : (i : ℕ) < mL
  · rw [dif_pos hlt, dif_pos hlt]
    by_cases hcase : mL - q ≤ i.val
    · have hcase' : mL - (q + 1) ≤ i.val := by omega
      simp [hcase, hcase']
    · have hcase' : ¬ mL - (q + 1) ≤ i.val := by omega
      simp [hcase, hcase']
  · rw [dif_neg hlt, dif_neg hlt]
    by_cases hcase : mR - (r - q) ≤ i.val - mL
    · have hcase' : mR - (r - (q + 1)) ≤ i.val - mL := by omega
      simp [hcase, hcase']
    · have hcase' : ¬ mR - (r - (q + 1)) ≤ i.val - mL := by omega
      simp [hcase, hcase']

/-- The neighbouring support of labels `q` and `q+1` is contained in the two
changing sites. -/
theorem labelRep_neighbor_support {mL mR r q : ℕ} (hq : q < mL) (hrq : q < r)
    (hrR : r - q ≤ mR) :
    support (labelRep mL mR r q) (labelRep mL mR r (q + 1)) ⊆
      {⟨leftSite mL q, by unfold leftSite; omega⟩,
       ⟨rightSite mL mR r q, by unfold rightSite; omega⟩} := by
  intro i hi
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra hnot
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  exact hi (labelRep_neighbor_agree hq hrq
    (by intro h; exact hnot.1 (Fin.ext h))
    (by intro h; exact hnot.2 (Fin.ext h)))

/-- The pattern on the two support sites is `(0,1)` for label `q` and `(1,0)`
for label `q+1`, exactly the `0101 → 1010` transition of Lemma S2. -/
theorem neighbor_pattern {mL mR r q : ℕ} (hq : q < mL) (hrq : q < r)
    (hrR : r - q ≤ mR) :
    labelRep mL mR r q ⟨leftSite mL q, by unfold leftSite; omega⟩ = false ∧
    labelRep mL mR r q ⟨rightSite mL mR r q, by unfold rightSite; omega⟩ = true ∧
    labelRep mL mR r (q + 1) ⟨leftSite mL q, by unfold leftSite; omega⟩ = true ∧
    labelRep mL mR r (q + 1) ⟨rightSite mL mR r q, by unfold rightSite; omega⟩ = false := by
  have hqR : r - (q + 1) ≤ mR := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [labelRep, concat]
    rw [dif_pos (by show leftSite mL q < mL; unfold leftSite; omega)]
    simp only [packed]
    have h : ¬ (mL - q ≤ leftSite mL q) := by unfold leftSite; omega
    simp [h]
  · simp only [labelRep, concat]
    rw [dif_neg (by show ¬ (rightSite mL mR r q < mL); unfold rightSite; omega)]
    simp only [packed]
    have h : mR - (r - q) ≤ rightSite mL mR r q - mL := by unfold rightSite; omega
    simp [h]
  · simp only [labelRep, concat]
    rw [dif_pos (by show leftSite mL q < mL; unfold leftSite; omega)]
    simp only [packed]
    have h : mL - (q + 1) ≤ leftSite mL q := by unfold leftSite; omega
    simp [h]
  · simp only [labelRep, concat]
    rw [dif_neg (by show ¬ (rightSite mL mR r q < mL); unfold rightSite; omega)]
    simp only [packed]
    have h : ¬ (mR - (r - (q + 1)) ≤ rightSite mL mR r q - mL) := by
      unfold rightSite; omega
    simp [h]

/-- The two changing sites are distinct, so the neighbouring support has
exactly two elements on an interior split. -/
theorem neighbor_support_card {mL mR r q : ℕ} (hq : q < mL) (hrq : q < r)
    (hrR : r - q ≤ mR) :
    (support (labelRep mL mR r q) (labelRep mL mR r (q + 1))).card = 2 := by
  have hsub := labelRep_neighbor_support (mL := mL) (mR := mR) (r := r) (q := q) hq hrq hrR
  have hpat := neighbor_pattern (mL := mL) (mR := mR) (r := r) (q := q) hq hrq hrR
  have hp1 : (⟨leftSite mL q, by unfold leftSite; omega⟩ : Fin (mL + mR)) ∈
      support (labelRep mL mR r q) (labelRep mL mR r (q + 1)) := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpat.1, hpat.2.2.1]
    simp
  have hp2 : (⟨rightSite mL mR r q, by unfold rightSite; omega⟩ : Fin (mL + mR)) ∈
      support (labelRep mL mR r q) (labelRep mL mR r (q + 1)) := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpat.2.1, hpat.2.2.2]
    simp
  have hne : (⟨leftSite mL q, by unfold leftSite; omega⟩ : Fin (mL + mR)) ≠
      ⟨rightSite mL mR r q, by unfold rightSite; omega⟩ := by
    intro h
    simp only [Fin.mk.injEq] at h
    unfold leftSite rightSite at h
    omega
  have hpair : ({⟨leftSite mL q, by unfold leftSite; omega⟩,
      ⟨rightSite mL mR r q, by unfold rightSite; omega⟩} : Finset (Fin (mL + mR))) ⊆
      support (labelRep mL mR r q) (labelRep mL mR r (q + 1)) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hp1
    · exact hp2
  have heq : support (labelRep mL mR r q) (labelRep mL mR r (q + 1)) =
      {⟨leftSite mL q, by unfold leftSite; omega⟩,
       ⟨rightSite mL mR r q, by unfold rightSite; omega⟩} :=
    Finset.Subset.antisymm hsub hpair
  rw [heq]
  exact Finset.card_pair hne

/-- Lemma S2, control-count half: at most four controls are needed, and they
all lie inside the block. -/
theorem neighbor_control_card (mL mR r q : ℕ) :
    (neighborControls mL mR r q).card ≤ 4 := by
  unfold neighborControls
  have himage : (Finset.univ.filter (fun i : Fin (mL + mR) =>
      i.val + 1 = leftSite mL q ∨ i.val = leftSite mL q + 1 ∨
      i.val + 1 = rightSite mL mR r q ∨ i.val = rightSite mL mR r q + 1)).image
      (fun i : Fin (mL + mR) => i.val) ⊆
      ({leftSite mL q - 1, leftSite mL q + 1,
        rightSite mL mR r q - 1, rightSite mL mR r q + 1} : Finset ℕ) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold leftSite rightSite at *
    rcases hi with h | h | h | h
    · have : i.val = mL - q - 1 - 1 := by omega
      simp [this]
    · have : i.val = mL - q - 1 + 1 := by omega
      simp [this]
    · have : i.val = mL + (mR - (r - q)) - 1 := by omega
      simp [this]
    · have : i.val = mL + (mR - (r - q)) + 1 := by omega
      simp [this]
  calc (Finset.univ.filter (fun i : Fin (mL + mR) =>
      i.val + 1 = leftSite mL q ∨ i.val = leftSite mL q + 1 ∨
      i.val + 1 = rightSite mL mR r q ∨ i.val = rightSite mL mR r q + 1)).card
      = ((Finset.univ.filter (fun i : Fin (mL + mR) =>
      i.val + 1 = leftSite mL q ∨ i.val = leftSite mL q + 1 ∨
      i.val + 1 = rightSite mL mR r q ∨ i.val = rightSite mL mR r q + 1)).image
        (fun i : Fin (mL + mR) => i.val)).card := by
          rw [Finset.card_image_of_injective]
          intro a b hab
          exact Fin.ext hab
    _ ≤ ({leftSite mL q - 1, leftSite mL q + 1,
        rightSite mL mR r q - 1, rightSite mL mR r q + 1} : Finset ℕ).card :=
        Finset.card_le_card himage
    _ ≤ 4 := by
        have h1 := Finset.card_insert_le (leftSite mL q - 1)
          ({leftSite mL q + 1, rightSite mL mR r q - 1, rightSite mL mR r q + 1} : Finset ℕ)
        have h2 := Finset.card_insert_le (leftSite mL q + 1)
          ({rightSite mL mR r q - 1, rightSite mL mR r q + 1} : Finset ℕ)
        have h3 := Finset.card_insert_le (rightSite mL mR r q - 1)
          ({rightSite mL mR r q + 1} : Finset ℕ)
        rw [Finset.card_singleton] at h3
        omega

/-- Eq. (S20): a block of size `m` carries at most `m` residual weights with
at most `m+1` labels each, so its Dicke `Λ` is at most `m(m+1) = O(m²)`, i.e.
the recursive expansion dimension is `d = 2`. -/
theorem dicke_lambda_le (m : ℕ) : m * (m + 1) ≤ 2 * m ^ 2 + 2 := by
  nlinarith [Nat.zero_le m]

/-- Geometric sum bound `∑_{t<T} 2^t ≤ 2^T`. -/
theorem sum_pow_two_le (T : ℕ) :
    (∑ t ∈ Finset.range T, (2 : ℝ) ^ t) ≤ (2 : ℝ) ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih]

/-- Eq. (S21): if the cutoff layer `T` satisfies `2^T k ≥ n`, the depth sum
`∑_t min(k, n/2^t)` is at most `k T + 2 k = O(k log(n/k))`. -/
theorem dicke_depth_le (n k : ℝ) (T H : ℕ) (_hk : 0 ≤ k) (hn : 0 ≤ n)
    (hcut : n ≤ (2 : ℝ) ^ T * k) :
    (∑ t ∈ Finset.range (T + H), min k (n / 2 ^ t)) ≤ k * (T : ℝ) + 2 * k := by
  rw [Finset.sum_range_add]
  have hhead : (∑ t ∈ Finset.range T, min k (n / 2 ^ t)) ≤ k * (T : ℝ) := by
    calc (∑ t ∈ Finset.range T, min k (n / 2 ^ t))
        ≤ ∑ _t ∈ Finset.range T, k := by
          apply Finset.sum_le_sum
          intro t _
          exact min_le_left _ _
      _ = k * (T : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have htail : (∑ s ∈ Finset.range H, min k (n / 2 ^ (T + s))) ≤ 2 * k := by
    have hterm : ∀ s ∈ Finset.range H,
        min k (n / 2 ^ (T + s)) ≤ (n / (2 : ℝ) ^ T) * ((1 / 2 : ℝ) ^ s) := by
      intro s _
      have hmin : min k (n / 2 ^ (T + s)) ≤ n / 2 ^ (T + s) := min_le_right _ _
      have hone : ((1 / 2 : ℝ) ^ s) * (2 : ℝ) ^ s = 1 := by
        rw [← mul_pow]
        norm_num
      have hsplit : n / (2 : ℝ) ^ (T + s) = (n / (2 : ℝ) ^ T) * ((1 / 2 : ℝ) ^ s) := by
        rw [pow_add]
        field_simp
        nlinarith [hone]
      rw [← hsplit]
      exact hmin
    calc (∑ s ∈ Finset.range H, min k (n / 2 ^ (T + s)))
        ≤ ∑ s ∈ Finset.range H, (n / (2 : ℝ) ^ T) * ((1 / 2 : ℝ) ^ s) :=
          Finset.sum_le_sum hterm
      _ = (n / (2 : ℝ) ^ T) * (∑ s ∈ Finset.range H, (1 / 2 : ℝ) ^ s) := by
          rw [Finset.mul_sum]
      _ ≤ (n / (2 : ℝ) ^ T) * 2 := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg hn (by positivity))
          exact geom_sum_le_two (by norm_num) (by norm_num) H
      _ ≤ 2 * k := by
          have hquot : n / (2 : ℝ) ^ T ≤ k := by
            rw [div_le_iff₀ (by positivity)]
            calc n ≤ (2 : ℝ) ^ T * k := hcut
              _ = k * (2 : ℝ) ^ T := by ring
          nlinarith
  linarith

/-- Eq. (S22): under the same cutoff conditions the gate sum
`∑_t 2^t min(k, n/2^t)²` is at most `2 n k + 2 n k = O(n k)`. -/
theorem dicke_gate_le (n k : ℝ) (T H : ℕ) (hk : 0 ≤ k) (hn : 0 ≤ n)
    (hcut : n ≤ (2 : ℝ) ^ T * k) (hcut' : (2 : ℝ) ^ T * k ≤ 2 * n) :
    (∑ t ∈ Finset.range (T + H), (2 : ℝ) ^ t * (min k (n / 2 ^ t)) ^ 2) ≤ 4 * n * k := by
  rw [Finset.sum_range_add]
  have hhead : (∑ t ∈ Finset.range T, (2 : ℝ) ^ t * (min k (n / 2 ^ t)) ^ 2) ≤ 2 * n * k := by
    have hterm : ∀ t ∈ Finset.range T,
        (2 : ℝ) ^ t * (min k (n / 2 ^ t)) ^ 2 ≤ (2 : ℝ) ^ t * k ^ 2 := by
      intro t _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : 0 ≤ min k (n / 2 ^ t) := le_min hk (div_nonneg hn (by positivity))
      have h2 : min k (n / 2 ^ t) ≤ k := min_le_left _ _
      nlinarith
    calc (∑ t ∈ Finset.range T, (2 : ℝ) ^ t * (min k (n / 2 ^ t)) ^ 2)
        ≤ ∑ t ∈ Finset.range T, (2 : ℝ) ^ t * k ^ 2 := Finset.sum_le_sum hterm
      _ = (∑ t ∈ Finset.range T, (2 : ℝ) ^ t) * k ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ T * k ^ 2 := by
          apply mul_le_mul_of_nonneg_right (sum_pow_two_le T) (by positivity)
      _ ≤ 2 * n * k := by
          have h := mul_le_mul_of_nonneg_right hcut' hk
          nlinarith
  have htail : (∑ s ∈ Finset.range H,
      (2 : ℝ) ^ (T + s) * (min k (n / 2 ^ (T + s))) ^ 2) ≤ 2 * n * k := by
    have hterm : ∀ s ∈ Finset.range H,
        (2 : ℝ) ^ (T + s) * (min k (n / 2 ^ (T + s))) ^ 2 ≤
          n ^ 2 / (2 : ℝ) ^ T * ((1 / 2 : ℝ) ^ s) := by
      intro s _
      have hmin : min k (n / 2 ^ (T + s)) ≤ n / 2 ^ (T + s) := min_le_right _ _
      have hminnn : 0 ≤ min k (n / 2 ^ (T + s)) := le_min hk (div_nonneg hn (by positivity))
      have hsq : (min k (n / 2 ^ (T + s))) ^ 2 ≤ (n / 2 ^ (T + s)) ^ 2 := by
        exact sq_le_sq' (by linarith [neg_nonpos.mpr hminnn]) hmin
      have hone : ((1 / 2 : ℝ) ^ s) * (2 : ℝ) ^ s = 1 := by
        rw [← mul_pow]
        norm_num
      have hval : (2 : ℝ) ^ (T + s) * (n / 2 ^ (T + s)) ^ 2 =
          n ^ 2 / (2 : ℝ) ^ T * ((1 / 2 : ℝ) ^ s) := by
        rw [pow_add]
        field_simp
        nlinarith [hone]
      calc (2 : ℝ) ^ (T + s) * (min k (n / 2 ^ (T + s))) ^ 2
          ≤ (2 : ℝ) ^ (T + s) * (n / 2 ^ (T + s)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = n ^ 2 / (2 : ℝ) ^ T * ((1 / 2 : ℝ) ^ s) := hval
    calc (∑ s ∈ Finset.range H,
          (2 : ℝ) ^ (T + s) * (min k (n / 2 ^ (T + s))) ^ 2)
        ≤ ∑ s ∈ Finset.range H, n ^ 2 / (2 : ℝ) ^ T * ((1 / 2 : ℝ) ^ s) :=
          Finset.sum_le_sum hterm
      _ = n ^ 2 / (2 : ℝ) ^ T * (∑ s ∈ Finset.range H, (1 / 2 : ℝ) ^ s) := by
          rw [Finset.mul_sum]
      _ ≤ n ^ 2 / (2 : ℝ) ^ T * 2 := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg n) (by positivity))
          exact geom_sum_le_two (by norm_num) (by norm_num) H
      _ ≤ 2 * n * k := by
          have hquot : n / (2 : ℝ) ^ T ≤ k := by
            rw [div_le_iff₀ (by positivity)]
            calc n ≤ (2 : ℝ) ^ T * k := hcut
              _ = k * (2 : ℝ) ^ T := by ring
          have hn2 : n ^ 2 / (2 : ℝ) ^ T * 2 = 2 * n * (n / (2 : ℝ) ^ T) := by
            field_simp
          rw [hn2]
          exact mul_le_mul_of_nonneg_left hquot (mul_nonneg (by norm_num) hn)
  nlinarith [hhead, htail]

end Qatlib.Papers.ProbStructure26.StatePrep
