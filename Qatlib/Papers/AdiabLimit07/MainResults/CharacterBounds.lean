/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabLimit07.MainResults.Definitions

/-!
# Walsh character and coupling bounds

Proves orthogonality and norm bounds for `walshChar`, together with cardinality identities for
the partition `qBlock`. These estimates bound a weighted coupling sum by the size of a block
complement and bound a sum of imaginary amplitude products for normalized vectors. See
[IoannouMosca2008].

## Main statements

* `walshChar_sum`: Summing the character gives the register cardinality on the diagonal and zero
  elsewhere.
* `coupling_bound`: A block coupling sum is controlled by `maxF` and the complement cardinality.
* `im_inner_sum_le_sqrt`: A normalized amplitude vector gives a square-root cardinality bound.

## References

* [Ioannou and Mosca, 2008][IoannouMosca2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n : ℕ}

/-- Every Walsh character value has complex norm one. -/
theorem walshChar_norm (z x y : Reg n) : ‖walshChar z x y‖ = 1 := by
  unfold walshChar
  rw [norm_prod]
  refine Finset.prod_eq_one ?_
  intro i _
  split_ifs <;> simp

/-- The sum of `walshChar z x y` over `z` is `2 ^ n` when `x = y` and zero otherwise. -/
theorem walshChar_sum (x y : Reg n) :
    (∑ z : Reg n, walshChar z x y) = if x = y then ((2 : ℕ) ^ n : ℂ) else 0 := by
  have hcongr : (∑ z : Reg n, walshChar z x y)
      = ∑ z : Reg n, ∏ i : Fin n,
          ((if (fun j => x j ^^ y j) i && z i then (-1 : ℂ) else 1) *
            (if (ZeroStr n) i && z i then (-1 : ℂ) else 1)) := by
    apply Finset.sum_congr rfl
    intro z _
    unfold walshChar
    apply Finset.prod_congr rfl
    intro i _
    simp [ZeroStr, Bool.and_comm]
  rw [hcongr, bv_orthogonality (n := n)]
  have hiff : (∀ i : Fin n, (fun j => x j ^^ y j) i = (ZeroStr n) i) ↔ x = y := by
    constructor
    · intro h
      funext i
      have hi := h i
      simp only [ZeroStr] at hi
      revert hi
      cases hx : x i <;> cases hy : y i <;> simp_all
    · intro h i
      subst h
      simp [ZeroStr]
  by_cases hxy : x = y
  · rw [if_pos (hiff.mpr hxy), if_pos hxy]
    push_cast
    ring
  · rw [if_neg (fun h => hxy (hiff.mp h)), if_neg hxy]

/-- The real cardinalities of the `qBlock` fibers sum to the number `2 ^ n` of register
configurations. -/
theorem sum_qBlock_card {q : ℕ} (qIdx : Reg n → Fin (q + 1)) :
    (∑ k : Fin (q + 1), ((qBlock qIdx k).card : ℝ)) = ((2 : ℕ) ^ n : ℝ) := by
  have hfib := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Reg n)))
    (f := qIdx) (t := (Finset.univ : Finset (Fin (q + 1)))) (fun x _ => Finset.mem_univ _)
  simp only [Finset.card_univ] at hfib
  rw [card_reg] at hfib
  have hsum : (∑ k : Fin (q + 1), (qBlock qIdx k).card) = 2 ^ n := hfib.symm
  calc
    (∑ k : Fin (q + 1), ((qBlock qIdx k).card : ℝ))
        = ((∑ k : Fin (q + 1), (qBlock qIdx k).card : ℕ) : ℝ) := by push_cast; ring
    _ = ((2 ^ n : ℕ) : ℝ) := by rw [hsum]
    _ = ((2 : ℕ) ^ n : ℝ) := by norm_num

/-- The norm of a Walsh character sum over a block is at most the cardinality of that block. -/
theorem walshChar_block_sum_norm_le {q : ℕ} (qIdx : Reg n → Fin (q + 1))
    (k : Fin (q + 1)) (x y : Reg n) :
    ‖∑ z ∈ qBlock qIdx k, walshChar z x y‖ ≤ ((qBlock qIdx k).card : ℝ) := by
  calc
    ‖∑ z ∈ qBlock qIdx k, walshChar z x y‖
        ≤ ∑ z ∈ qBlock qIdx k, ‖walshChar z x y‖ := norm_sum_le _ _
    _ = ∑ _z ∈ qBlock qIdx k, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [walshChar_norm]
    _ = ((qBlock qIdx k).card : ℝ) := by simp

/-- For nonnegative monotone energy values bounded by `maxF`, the weighted character coupling is
bounded by `maxF` times the complement cardinality of block `K`. -/
theorem coupling_bound {q : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) (K : Fin (q + 1))
    (hmono : ∀ a b : Fin (q + 1), a ≤ b → F a ≤ F b)
    (hF0 : 0 ≤ F 0) (maxF : ℝ) (hmax : ∀ k, F k ≤ maxF) (x y : Reg n) :
    ‖∑ k : Fin (q + 1),
        ((F K - F k : ℝ) : ℂ) * (∑ z ∈ qBlock qIdx k, walshChar z x y)‖
      ≤ maxF * (((2 : ℕ) ^ n : ℝ) - ((qBlock qIdx K).card : ℝ)) := by
  have hmax0 : 0 ≤ maxF := le_trans hF0 (hmax 0)
  have hnonneg : ∀ k : Fin (q + 1), 0 ≤ F k := fun k => le_trans hF0 (hmono 0 k (Fin.zero_le k))

  have hterm : ∀ k : Fin (q + 1),
      ‖((F K - F k : ℝ) : ℂ) * (∑ z ∈ qBlock qIdx k, walshChar z x y)‖
        ≤ if k = K then 0 else maxF * ((qBlock qIdx k).card : ℝ) := by
    intro k
    by_cases hk : k = K
    · subst hk
      simp
    · rw [if_neg hk, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hS := walshChar_block_sum_norm_le qIdx k x y
      have hFK : |F K - F k| ≤ maxF := by
        have h1 : F K - F k ≤ maxF := by linarith [hmax K, hnonneg k]
        have h2 : -(maxF) ≤ F K - F k := by linarith [hmax k, hnonneg K]
        exact abs_le.mpr ⟨h2, h1⟩
      exact mul_le_mul hFK hS (by positivity) hmax0
  have hsum_le : ‖∑ k : Fin (q + 1),
        ((F K - F k : ℝ) : ℂ) * (∑ z ∈ qBlock qIdx k, walshChar z x y)‖
      ≤ ∑ k : Fin (q + 1), (if k = K then 0 else maxF * ((qBlock qIdx k).card : ℝ)) := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum (fun k _ => hterm k)

  have hErase : (∑ k : Fin (q + 1),
        (if k = K then 0 else maxF * ((qBlock qIdx k).card : ℝ)))
      = maxF * (((2 : ℕ) ^ n : ℝ) - ((qBlock qIdx K).card : ℝ)) := by
    rw [← Finset.sum_erase (s := (Finset.univ : Finset (Fin (q + 1)))) (a := K)
      (f := fun k => if k = K then 0 else maxF * ((qBlock qIdx k).card : ℝ)) (by simp)]
    have hcongr : (∑ k ∈ (Finset.univ : Finset (Fin (q + 1))).erase K,
          (if k = K then 0 else maxF * ((qBlock qIdx k).card : ℝ)))
        = ∑ k ∈ (Finset.univ : Finset (Fin (q + 1))).erase K,
            maxF * ((qBlock qIdx k).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_neg (Finset.ne_of_mem_erase hk)]
    rw [hcongr, ← Finset.mul_sum]
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (q + 1))))
      (f := fun k => ((qBlock qIdx k).card : ℝ)) (Finset.mem_univ K)
    rw [sum_qBlock_card qIdx] at hsplit
    congr 1
    rw [eq_sub_iff_add_eq]
    exact hsplit
  calc
    ‖∑ k, ((F K - F k : ℝ) : ℂ) * (∑ z ∈ qBlock qIdx k, walshChar z x y)‖
        ≤ ∑ k, (if k = K then 0 else maxF * ((qBlock qIdx k).card : ℝ)) := hsum_le
    _ = maxF * (((2 : ℕ) ^ n : ℝ) - ((qBlock qIdx K).card : ℝ)) := hErase

/-- For normalized amplitudes, the sum of absolute imaginary parts of `γ w * conj (γ y)` is at
most the square root of the register cardinality. -/
theorem im_inner_sum_le_sqrt {γ : Reg n → ℂ} (hγ : Normalized γ) (w : Reg n) :
    (∑ y : Reg n, |(γ w * (starRingEnd ℂ) (γ y)).im|) ≤ Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
  have hterm_sq : ∀ y : Reg n, ‖γ y‖ ^ 2 ≤ 1 := by
    intro y
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset (Reg n)))
      (f := fun y => ‖γ y‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ y)
    simpa [Normalized] using hle.trans_eq hγ
  have hw : ‖γ w‖ ≤ 1 := by
    have h2 := hterm_sq w
    nlinarith [norm_nonneg (γ w)]
  have hcard : (∑ _y : Reg n, (1 : ℝ)) = ((2 : ℕ) ^ n : ℝ) := by
    simp [Finset.sum_const, card_reg]
  have hnorm_sum : (∑ y : Reg n, ‖γ y‖) ≤ Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by
    calc
      (∑ y : Reg n, ‖γ y‖) = ∑ y : Reg n, (1 : ℝ) * ‖γ y‖ := by simp
      _ ≤ Real.sqrt (∑ y : Reg n, (1 : ℝ) ^ 2) * Real.sqrt (∑ y : Reg n, ‖γ y‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt (((2 : ℕ) ^ n : ℝ)) * 1 := by
          rw [hγ]
          simp only [one_pow, Real.sqrt_one, mul_one]
          rw [hcard]
      _ = Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by ring
  calc
    (∑ y : Reg n, |(γ w * (starRingEnd ℂ) (γ y)).im|)
        ≤ ∑ y : Reg n, ‖γ w‖ * ‖γ y‖ := by
          apply Finset.sum_le_sum
          intro y _
          calc
            |(γ w * (starRingEnd ℂ) (γ y)).im| ≤ ‖γ w * (starRingEnd ℂ) (γ y)‖ :=
              Complex.abs_im_le_norm _
            _ = ‖γ w‖ * ‖γ y‖ := by rw [norm_mul, starRingEnd_apply, norm_star]
    _ = ‖γ w‖ * (∑ y : Reg n, ‖γ y‖) := by rw [Finset.mul_sum]
    _ ≤ 1 * Real.sqrt (((2 : ℕ) ^ n : ℝ)) :=
        mul_le_mul hw hnorm_sum (by positivity) (by positivity)
    _ = Real.sqrt (((2 : ℕ) ^ n : ℝ)) := by ring

end Qatlib.Papers.AdiabLimit07.MainResults
