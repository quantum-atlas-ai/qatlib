/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Lemma4PromiseProbability

/-!
# Counting sign-sum promise strings

Relates sign sums of Boolean strings to their number of true bits and counts the corresponding
level sets by binomial coefficients. Bitwise complementation identifies positive and negative
levels, yielding an exact formula for `probOf` on the parity-adjusted promise set. See
[ChildsKothari2010] for the surrounding analysis.

## Main statements

* `card_signSum_pos`: For `B ≤ M` of the same parity as `M`, the number of strings with sign sum
  `B` is `M.choose ((M + B) / 2)`.
* `card_promiseStrings`: For positive `B ≤ M` of the same parity as `M`, the promise set has
  cardinality `2 * M.choose ((M + B) / 2)`.
* `probOf_promiseSet_eq`: If `0 < promiseB M ≤ M`, the promise-set probability is `2 * M.choose
  ((M + promiseB M) / 2) / 2^M`.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option autoImplicit false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

/-- Negating a Boolean bit negates its real sign. -/
lemma signOf_not (b : Bool) : signOf (!b) = -signOf b := by
  cases b <;> simp [signOf]

/-- The sum of the signs of a length-`M` Boolean string is twice its number of true bits minus
`M` [ChildsKothari2010]. -/
lemma signSum_eq (M : ℕ) (b : Fin M → Bool) :
    ∑ i, signVec b i
      = 2 * ((Finset.univ.filter (fun i => b i)).card : ℝ) - (M : ℝ) := by
  have hpt : ∀ i : Fin M, signVec b i = 2 * (if b i then (1 : ℝ) else 0) - 1 := by
    intro i
    cases hbi : b i <;> simp [signVec, signOf, hbi]
    norm_num
  have hcount : (∑ i : Fin M, (if b i then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun i => b i)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  calc ∑ i, signVec b i
      = ∑ i : Fin M, (2 * (if b i then (1 : ℝ) else 0) - 1) :=
        Finset.sum_congr rfl fun i _ => hpt i
    _ = 2 * (∑ i : Fin M, (if b i then (1 : ℝ) else 0)) - (M : ℝ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [Finset.card_univ]
    _ = 2 * ((Finset.univ.filter (fun i => b i)).card : ℝ) - (M : ℝ) := by
        rw [hcount]

/-- If `B` and `M` have the same parity, then `M + B` is divisible by two. -/
lemma two_dvd_add_of_mod_two_eq {M B : ℕ} (hpar : B % 2 = M % 2) : 2 ∣ M + B := by
  refine Nat.dvd_of_mod_eq_zero ?_
  rw [Nat.add_mod, hpar, ← two_mul]
  exact Nat.mul_mod_right 2 (M % 2)

/-- For `B ≤ M` of the same parity as `M`, sign sum `B` is equivalent to having exactly `(M + B)
/ 2` true bits [ChildsKothari2010]. -/
lemma signSum_eq_iff (M B : ℕ) (_hBM : B ≤ M) (hpar : B % 2 = M % 2) (b : Fin M → Bool) :
    (∑ i, signVec b i = (B : ℝ)) ↔
      (Finset.univ.filter (fun i => b i)).card = (M + B) / 2 := by
  have hdvd : 2 ∣ M + B := two_dvd_add_of_mod_two_eq hpar
  rw [signSum_eq]
  constructor
  · intro h
    have h' : (2 : ℝ) * ((Finset.univ.filter (fun i => b i)).card : ℝ)
        = (M : ℝ) + (B : ℝ) := by linarith
    have h2 : 2 * (Finset.univ.filter (fun i => b i)).card = M + B := by
      exact_mod_cast h'
    rw [← h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · intro h
    have h2 : 2 * ((M + B) / 2) = M + B := Nat.mul_div_cancel' hdvd
    have h2R : (2 : ℝ) * (((M + B) / 2 : ℕ) : ℝ) = (M : ℝ) + (B : ℝ) := by
      exact_mod_cast h2
    rw [h]
    linarith

/-- For `B ≤ M` of the same parity as `M`, the number of strings with sign sum `B` is `M.choose
((M + B) / 2)` [ChildsKothari2010]. -/
theorem card_signSum_pos (M B : ℕ) (hBM : B ≤ M) (hpar : B % 2 = M % 2) :
    (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = (B : ℝ))).card
      = M.choose ((M + B) / 2) := by
  classical
  have hfilter : Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = (B : ℝ))
      = Finset.univ.filter (fun b : Fin M → Bool =>
          (Finset.univ.filter (fun i : Fin M => b i)).card = (M + B) / 2) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact signSum_eq_iff M B hBM hpar b
  rw [hfilter]
  have hcard :
      (Finset.univ.filter (fun b : Fin M → Bool =>
          (Finset.univ.filter (fun i : Fin M => b i)).card = (M + B) / 2)).card
        = ((Finset.univ : Finset (Fin M)).powersetCard ((M + B) / 2)).card := by
    refine Finset.card_bij (fun b _ => Finset.univ.filter (fun i => b i)) ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hb⟩
    · intro a1 _ a2 _ h
      funext i
      have h' : (Finset.univ.filter (fun j : Fin M => a1 j))
          = (Finset.univ.filter (fun j : Fin M => a2 j)) := h
      have hiff : (i ∈ Finset.univ.filter (fun j => a1 j)) ↔
          (i ∈ Finset.univ.filter (fun j => a2 j)) := by rw [h']
      have hiff' : (a1 i = true) ↔ (a2 i = true) := by simpa using hiff
      cases h1 : a1 i <;> cases h2 : a2 i <;> simp_all
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hfix : Finset.univ.filter (fun i : Fin M => decide (i ∈ s)) = s := by
          ext i
          simp
        rw [hfix, hs.2]
      · ext i
        simp
  rw [hcard, Finset.card_powersetCard]
  simp

/-- Bitwise complementation negates the sum of the associated signs. -/
lemma signSum_not (M : ℕ) (b : Fin M → Bool) :
    ∑ i, signVec (fun j => !b j) i = -∑ i, signVec b i := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact signOf_not (b i)

/-- The numbers of strings with sign sums `-B` and `B` are equal [ChildsKothari2010]. -/
lemma card_signSum_neg (M B : ℕ) :
    (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = -(B : ℝ))).card
      = (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = (B : ℝ))).card := by
  classical
  refine Finset.card_bijective (fun b : Fin M → Bool => fun i => !b i) ?_ ?_
  · constructor
    · intro b1 b2 h
      funext i
      have h' : (!b1 i) = (!b2 i) := congrFun h i
      revert h'
      cases b1 i <;> cases b2 i <;> simp
    · intro b
      exact ⟨fun i => !b i, by funext i; simp⟩
  · intro b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [signSum_not]
    constructor <;> intro h <;> linarith

/-- For positive `B ≤ M` of the same parity as `M`, the promise set has cardinality `2 *
M.choose ((M + B) / 2)` [ChildsKothari2010]. -/
theorem card_promiseStrings (M B : ℕ) (hBM : B ≤ M) (hpos : 0 < B) (hpar : B % 2 = M % 2) :
    (promiseStrings M B).card = 2 * M.choose ((M + B) / 2) := by
  classical
  have hunion : promiseStrings M B
      = (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = (B : ℝ)))
        ∪ (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = -(B : ℝ))) := by
    unfold promiseStrings
    rw [Finset.filter_or]
  have hdisj : Disjoint
      (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = (B : ℝ)))
      (Finset.univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = -(B : ℝ))) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb1 hb2
    have hBB : (B : ℝ) = -(B : ℝ) := hb1.symm.trans hb2
    have hzero : (B : ℝ) = 0 := by linarith
    have : B = 0 := by exact_mod_cast hzero
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, card_signSum_pos M B hBM hpar,
    card_signSum_neg M B, card_signSum_pos M B hBM hpar]
  ring

/-- The bias `promiseB M` has the same parity as `M` [ChildsKothari2010]. -/
lemma promiseB_mod_two (M : ℕ) : promiseB M % 2 = M % 2 := by
  unfold promiseB
  rw [Nat.add_mod, Nat.mul_mod_right 2
    (Nat.floor (Real.sqrt (M * Real.log (M : ℝ)) / 2))]
  simp [Nat.mod_eq_of_lt (Nat.mod_lt M (by norm_num : 0 < 2))]

/-- If `0 < promiseB M ≤ M`, the promise-set probability is `2 * M.choose ((M + promiseB M) / 2)
/ 2^M` [ChildsKothari2010]. -/
theorem probOf_promiseSet_eq (M : ℕ) (hBM : promiseB M ≤ M) (hpos : 0 < promiseB M) :
    probOf M (fun b => b ∈ promiseSet M)
      = 2 * (M.choose ((M + promiseB M) / 2) : ℝ) / (2 : ℝ) ^ M := by
  classical
  have hfilter : (Finset.univ.filter (fun b : Fin M → Bool => b ∈ promiseSet M))
      = promiseSet M := by
    ext b
    simp
  have hmain : ((Finset.univ.filter (fun b : Fin M → Bool => b ∈ promiseSet M)).card : ℝ)
      / (2 : ℝ) ^ M = 2 * (M.choose ((M + promiseB M) / 2) : ℝ) / (2 : ℝ) ^ M := by
    rw [hfilter]
    unfold promiseSet
    rw [card_promiseStrings M (promiseB M) hBM hpos (promiseB_mod_two M)]
    push_cast
    ring
  simpa [probOf] using hmain

end Qatlib.Papers.NonSparseHam09.MainResults
