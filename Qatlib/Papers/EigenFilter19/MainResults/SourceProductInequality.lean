/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# EigenFilter19 -- Lemma 14 (product vs. sum inequality)

Fixed source: arXiv:1910.14596 (accepted Quantum 2020-11-06), Lemma 14, printed p. 33
(Appendix G).

The paper states: if `0 < a_j < 1` and `0 < b_j < 1` for `j = 0, ..., R-1`, then

  `prod_{j=0}^{R-1} (a_j - b_j) >= prod_{j=0}^{R-1} a_j - sum_{j=0}^{R-1} b_j`.

It is used to lower-bound the success probability of the Quantum-Zeno-effect QLSP
algorithm (Appendix G, Eq. (A13)), where `a_j` is the success amplitude of one
projection step and `b_j` the loss.

Formalization boundary. Indices `j = 0, ..., R-1` are represented by `Finset.range R`
applied to functions `Nat -> Real`. The proof below is the paper's telescoping
argument, made fully explicit: define the cut products

  `F k = prod_{j<k}(a_j - b_j) * prod_{k<=j<R} a_j`,

so that `F 0 = prod a`, `F R = prod (a-b)`, and

  `F k - F (k+1) = (prod_{j<k}(a_j - b_j)) * b_k * (prod_{j>k} a_j)`.

Each difference is at most `b_k` because the first product is bounded by one in
absolute value (all factors lie in `(-1,1)`) and the second by one (all factors lie in
`(0,1)`); summing gives the claim. This mechanises the paper's remark that the
inequality "can be easily proved using induction".
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Qatlib.Papers.EigenFilter19.MainResults

/-- Source Lemma 14 (arXiv:1910.14596 p. 33). For `0 < a_j, b_j < 1` with
`j = 0, ..., R-1`, `prod (a_j - b_j) >= prod a_j - sum b_j`. -/
theorem source_lemma14_product (R : ℕ) (a b : ℕ → ℝ)
    (ha0 : ∀ j < R, 0 < a j) (ha1 : ∀ j < R, a j < 1)
    (hb0 : ∀ j < R, 0 < b j) (hb1 : ∀ j < R, b j < 1) :
    (∏ j ∈ Finset.range R, a j) - (∑ j ∈ Finset.range R, b j) ≤ ∏ j ∈ Finset.range R, (a j - b j) := by
  -- The cut-product family.
  let F : ℕ → ℝ := fun k =>
    (∏ j ∈ Finset.range k, (a j - b j)) * (∏ j ∈ Finset.Ico k R, a j)
  have hIco0 : Finset.Ico 0 R = Finset.range R := by
    ext j
    simp
  have hF0 : F 0 = ∏ j ∈ Finset.range R, a j := by
    dsimp only [F]
    rw [Finset.prod_range_zero, one_mul, hIco0]
  have hFR : F R = ∏ j ∈ Finset.range R, (a j - b j) := by
    dsimp only [F]
    rw [Finset.Ico_self, Finset.prod_empty, mul_one]
  -- One telescoping step.
  have hstep : ∀ k, k < R → F k - F (k + 1) =
      (∏ j ∈ Finset.range k, (a j - b j)) * b k * (∏ j ∈ Finset.Ico (k + 1) R, a j) := by
    intro k hk
    have hIco : Finset.Ico k R = insert k (Finset.Ico (k + 1) R) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      constructor
      · rintro ⟨hkj, hjR⟩
        rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨Nat.succ_le_of_lt hlt, hjR⟩
      · rintro (rfl | ⟨hk1, hjR⟩)
        · exact ⟨le_rfl, hk⟩
        · exact ⟨le_trans (Nat.le_succ k) hk1, hjR⟩
    have hknot : k ∉ Finset.Ico (k + 1) R := by
      intro hmem
      exact absurd (Finset.mem_Ico.mp hmem).1 (Nat.not_succ_le_self k)
    have hprodIco : (∏ j ∈ Finset.Ico k R, a j) =
        a k * ∏ j ∈ Finset.Ico (k + 1) R, a j := by
      rw [hIco, Finset.prod_insert hknot]
    have hprodRange : (∏ j ∈ Finset.range (k + 1), (a j - b j)) =
        (∏ j ∈ Finset.range k, (a j - b j)) * (a k - b k) := by
      rw [Finset.prod_range_succ]
    dsimp only [F]
    rw [hprodRange, hprodIco]
    ring
  -- Each telescoping term is at most `b k`.
  have hbound : ∀ k ∈ Finset.range R, F k - F (k + 1) ≤ b k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hstep k hk]
    -- each factor `a j - b j` lies in `[-1,1]`
    have hc : ∀ j < R, |a j - b j| ≤ 1 := by
      intro j hjR
      have h1 : a j - b j ≤ 1 := by linarith [ha1 j hjR, hb0 j hjR]
      have h2 : -1 ≤ a j - b j := by linarith [ha0 j hjR, hb1 j hjR]
      exact abs_le.mpr ⟨h2, h1⟩
    have hGabs : |∏ j ∈ Finset.range k, (a j - b j)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _)
        (fun j hj => hc j (lt_trans (Finset.mem_range.mp hj) hk))
    have hG : (∏ j ∈ Finset.range k, (a j - b j)) ≤ 1 :=
      le_trans (le_abs_self _) hGabs
    have hHnonneg : 0 ≤ ∏ j ∈ Finset.Ico (k + 1) R, a j :=
      Finset.prod_nonneg (fun j hj => le_of_lt (ha0 j (Finset.mem_Ico.mp hj).2))
    have hH : (∏ j ∈ Finset.Ico (k + 1) R, a j) ≤ 1 :=
      Finset.prod_le_one₀
        (fun j hj => le_of_lt (ha0 j (Finset.mem_Ico.mp hj).2))
        (fun j hj => le_of_lt (ha1 j (Finset.mem_Ico.mp hj).2))
    have hGH : (∏ j ∈ Finset.range k, (a j - b j)) *
        (∏ j ∈ Finset.Ico (k + 1) R, a j) ≤ 1 :=
      calc (∏ j ∈ Finset.range k, (a j - b j)) * (∏ j ∈ Finset.Ico (k + 1) R, a j)
          ≤ 1 * (∏ j ∈ Finset.Ico (k + 1) R, a j) :=
            mul_le_mul_of_nonneg_right hG hHnonneg
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hH (by norm_num)
        _ = 1 := by ring
    calc (∏ j ∈ Finset.range k, (a j - b j)) * b k * (∏ j ∈ Finset.Ico (k + 1) R, a j)
        = b k * ((∏ j ∈ Finset.range k, (a j - b j)) *
            (∏ j ∈ Finset.Ico (k + 1) R, a j)) := by ring
      _ ≤ b k * 1 := mul_le_mul_of_nonneg_left hGH (le_of_lt (hb0 k hk))
      _ = b k := by ring
  -- Telescope and conclude.
  have htel : (∑ k ∈ Finset.range R, (F k - F (k + 1))) = F 0 - F R := by
    have h := Finset.sum_range_sub F R
    have hneg : (∑ k ∈ Finset.range R, (F k - F (k + 1))) =
        -(∑ k ∈ Finset.range R, (F (k + 1) - F k)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hneg, h]
    ring
  have hsum : (∑ k ∈ Finset.range R, (F k - F (k + 1))) ≤ ∑ k ∈ Finset.range R, b k :=
    Finset.sum_le_sum hbound
  have hQP : (∏ j ∈ Finset.range R, a j) - (∏ j ∈ Finset.range R, (a j - b j)) ≤
      ∑ k ∈ Finset.range R, b k := by
    calc (∏ j ∈ Finset.range R, a j) - (∏ j ∈ Finset.range R, (a j - b j))
        = F 0 - F R := by rw [← hF0, ← hFR]
      _ = ∑ k ∈ Finset.range R, (F k - F (k + 1)) := htel.symm
      _ ≤ ∑ k ∈ Finset.range R, b k := hsum
  linarith

end Qatlib.Papers.EigenFilter19.MainResults
