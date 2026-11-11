/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Qatlib.Papers.QWalkDiff01.MainResults.Defs

/-!
# Absorbing chain on the right tree

The transition kernel `rightStep` defines a finite chain with a right root and a sink, and
`rightDist` evolves the point mass at state zero. The harmonic function `barrier` controls the
probability of reaching the root in the classical propagation analysis of
[ChildsFarhiGutmann2002].

## Main statements

* `barrier_harmonic`: the barrier is preserved by one step for positive depth.
* `rightDist_root_le`: the root mass is at most `2⁻ⁿ` at every discrete time.

## References

* [Childs et al., 2002][ChildsFarhiGutmann2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- The next index in `Fin m`, with the final index fixed. -/
def upNbr {m : ℕ} (j : Fin m) : Fin m := if h : j.val + 1 < m then ⟨j.val + 1, h⟩ else j

/-- The preceding index in `Fin m`, with zero fixed. -/
def downNbr {m : ℕ} (j : Fin m) : Fin m := if h : 0 < j.val then ⟨j.val - 1, by omega⟩ else j

/-- Below the final index, `upNbr` increases the index by one. -/
lemma upNbr_eq {m : ℕ} {j : Fin m} (h : j.val + 1 < m) : upNbr j = ⟨j.val + 1, h⟩ := by
  simp [upNbr, dif_pos h]

/-- At a positive index, `downNbr` decreases the index by one. -/
lemma downNbr_eq {m : ℕ} {j : Fin m} (h : 0 < j.val) : downNbr j = ⟨j.val - 1, by omega⟩ := by
  simp [downNbr, dif_pos h]

/-- The transition weights of the right-tree chain, with upward probability `1/3`, downward
probability `2/3`, and special root and sink transitions. -/
def rightStep (n : ℕ) (j : Fin (n + 2)) : Fin (n + 2) → ℝ :=
  fun k =>
    if j.val = 0 then
      (if k.val = 1 then 1 / 2 else 0) + (if k.val = n + 1 then 1 / 2 else 0)
    else if j.val = n then (if k.val = n then 1 else 0)
    else if j.val = n + 1 then (if k.val = n + 1 then 1 else 0)
    else (if k.val = j.val + 1 then 1 / 3 else 0) + (if k.val = j.val - 1 then 2 / 3 else 0)

/-- The one-step expectation of `f` under the right-tree transition kernel. -/
def stepImage (n : ℕ) (f : Fin (n + 2) → ℝ) (j : Fin (n + 2)) : ℝ :=
  if j.val = 0 then (1 / 2) * f ⟨1, by omega⟩ + (1 / 2) * f ⟨n + 1, by omega⟩
  else if j.val = n then f j
  else if j.val = n + 1 then f j
  else (1 / 3) * f (upNbr j) + (2 / 3) * f (downNbr j)

/-- The distribution obtained by iterating `rightStep` from the point mass at state zero. -/
def rightDist (n : ℕ) : ℕ → Fin (n + 2) → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | T + 1 => fun k => ∑ j, rightDist n T j * rightStep n j k

/-- The value `2^m / 2^n`, except that the sink index `n + 1` has value zero. -/
def bval (n : ℕ) (m : ℕ) : ℝ := if m = n + 1 then 0 else (2 : ℝ) ^ m / (2 : ℝ) ^ n

/-- The barrier function on the right-tree state space, obtained by evaluating `bval` at each
index. -/
def barrier (n : ℕ) (j : Fin (n + 2)) : ℝ := bval n j.val

/-- A sum supported at a single index equals its weight times the value of the summand there. -/
lemma sum_single_val {m : ℕ} (f : Fin m → ℝ) {a : ℕ} (ha : a < m) (p : ℝ) :
    ∑ k : Fin m, (if k.val = a then p else 0) * f k = p * f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin m)]
  · simp
  · intro k _ hk
    have hka : k.val ≠ a := by
      intro h
      exact hk (Fin.ext (by simpa using h))
    simp [hka]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A sum of two weighted point masses evaluates to the corresponding two weighted function
values. -/
lemma sum_two_vals {m : ℕ} (f : Fin m → ℝ) {a b : ℕ} (ha : a < m) (hb : b < m)
    (p q : ℝ) :
    ∑ k : Fin m, ((if k.val = a then p else 0) + (if k.val = b then q else 0)) * f k
      = p * f ⟨a, ha⟩ + q * f ⟨b, hb⟩ := by
  rw [Finset.sum_congr rfl (fun k _ => by rw [add_mul]),
    Finset.sum_add_distrib, sum_single_val f ha p, sum_single_val f hb q]

/-- Every transition weight of `rightStep` is nonnegative. -/
lemma rightStep_nonneg (n : ℕ) (j k : Fin (n + 2)) : 0 ≤ rightStep n j k := by
  unfold rightStep
  split_ifs <;> norm_num

/-- Summing `f` against a row of `rightStep` gives `stepImage n f`. -/
lemma rightStep_expect (n : ℕ) (f : Fin (n + 2) → ℝ) (j : Fin (n + 2)) :
    ∑ k, rightStep n j k * f k = stepImage n f j := by
  by_cases h0 : j.val = 0
  · simp only [stepImage, rightStep, if_pos h0]
    exact sum_two_vals f (by omega : (1 : ℕ) < n + 2) (by omega : n + 1 < n + 2)
      (1 / 2) (1 / 2)
  · by_cases hn : j.val = n
    · simp only [stepImage, rightStep, if_neg h0, if_pos hn]
      rw [sum_single_val f (by omega : n < n + 2) 1, one_mul]
      exact congrArg f (Fin.ext (by simpa using hn)).symm
    · by_cases hs : j.val = n + 1
      · simp only [stepImage, rightStep, if_neg h0, if_neg hn, if_pos hs]
        rw [sum_single_val f (by omega : n + 1 < n + 2) 1, one_mul]
        exact congrArg f (Fin.ext (by simpa using hs)).symm
      · simp only [stepImage, rightStep, if_neg h0, if_neg hn, if_neg hs]
        rw [sum_two_vals f (by omega : j.val + 1 < n + 2) (by omega : j.val - 1 < n + 2)
          (1 / 3) (2 / 3), upNbr_eq (by omega), downNbr_eq (by omega)]

/-- Each row of the right-tree transition kernel has total mass one. -/
lemma rightStep_sum (n : ℕ) (j : Fin (n + 2)) : ∑ k, rightStep n j k = 1 := by
  have h := rightStep_expect n (fun _ => (1 : ℝ)) j
  have h1 : stepImage n (fun _ => (1 : ℝ)) j = 1 := by
    unfold stepImage
    split_ifs <;> norm_num
  simpa [h1] using h

/-- Every value of `bval` is nonnegative. -/
lemma bval_nonneg (n : ℕ) (m : ℕ) : 0 ≤ bval n m := by
  unfold bval
  split_ifs <;> positivity

/-- The right-tree barrier is nonnegative at every state. -/
lemma barrier_nonneg (n : ℕ) (j : Fin (n + 2)) : 0 ≤ barrier n j := bval_nonneg n j.val

/-- The barrier value at index zero is `(1 / 2)^n`. -/
lemma bval_zero (n : ℕ) : bval n 0 = (1 / 2 : ℝ) ^ n := by
  unfold bval
  rw [if_neg (by omega)]
  have h : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [h, inv_pow, div_eq_mul_inv, pow_zero, one_mul]

/-- The barrier value at the root index `n` is one. -/
lemma bval_mid (n : ℕ) : bval n n = 1 := by
  unfold bval
  rw [if_neg (by omega)]
  exact div_self (by positivity)

/-- The barrier value at the sink index `n + 1` is zero. -/
lemma bval_sink (n : ℕ) : bval n (n + 1) = 0 := by
  unfold bval
  rw [if_pos rfl]

/-- For `n ≥ 1`, the barrier is harmonic for the right-tree chain. -/
lemma barrier_harmonic (n : ℕ) (hn : 1 ≤ n) (j : Fin (n + 2)) :
    stepImage n (barrier n) j = barrier n j := by
  unfold stepImage
  by_cases h0 : j.val = 0
  · rw [if_pos h0]
    have hj : barrier n j = bval n 0 := by rw [barrier, h0]
    rw [hj]
    show (1 / 2) * bval n 1 + (1 / 2) * bval n (n + 1) = bval n 0
    rw [bval_sink, mul_zero, add_zero]
    have hb1 : bval n 1 = 2 / (2 : ℝ) ^ n := by
      unfold bval
      rw [if_neg (by omega)]
      norm_num
    rw [hb1, bval_zero]
    have h2 : (1 / 2 : ℝ) * (2 / (2 : ℝ) ^ n) = (1 / 2 : ℝ) ^ n := by
      have hc : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      rw [hc, inv_pow, div_eq_mul_inv, ← mul_assoc]
      norm_num
    rw [h2]
  · rw [if_neg h0]
    by_cases hn' : j.val = n
    · rw [if_pos hn']
    · rw [if_neg hn']
      by_cases hs : j.val = n + 1
      · rw [if_pos hs]
      · rw [if_neg hs]
        have hjpos : 0 < j.val := by omega
        have hu : upNbr j = (⟨j.val + 1, by omega⟩ : Fin (n + 2)) := upNbr_eq (by omega)
        have hd : downNbr j = (⟨j.val - 1, by omega⟩ : Fin (n + 2)) := downNbr_eq hjpos
        rw [hu, hd]
        have hne1 : (⟨j.val + 1, by omega⟩ : Fin (n + 2)).val ≠ n + 1 := by
          (try dsimp only)
          omega
        have hne2 : (⟨j.val - 1, by omega⟩ : Fin (n + 2)).val ≠ n + 1 := by
          (try dsimp only)
          omega
        have hbu : barrier n (⟨j.val + 1, by omega⟩ : Fin (n + 2)) =
            (2 : ℝ) ^ (j.val + 1) / (2 : ℝ) ^ n := by
          unfold barrier bval
          rw [if_neg hne1]
        have hbd : barrier n (⟨j.val - 1, by omega⟩ : Fin (n + 2)) =
            (2 : ℝ) ^ (j.val - 1) / (2 : ℝ) ^ n := by
          unfold barrier bval
          rw [if_neg hne2]
        have hbj : barrier n j = (2 : ℝ) ^ j.val / (2 : ℝ) ^ n := by
          unfold barrier bval
          rw [if_neg (by simpa using hs)]
        rw [hbu, hbd, hbj]
        have hpowj : (2 : ℝ) ^ j.val = (2 : ℝ) ^ (j.val - 1) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        have hpowj1 : (2 : ℝ) ^ (j.val + 1) = (2 : ℝ) ^ (j.val - 1) * 4 := by
          rw [show j.val + 1 = (j.val - 1) + 2 by omega, pow_add]
          norm_num
        rw [hpowj1, hpowj]
        field_simp
        ring

/-- The right-tree distribution has nonnegative entries at every time. -/
lemma rightDist_nonneg (n : ℕ) : ∀ (T : ℕ) (k : Fin (n + 2)), 0 ≤ rightDist n T k := by
  intro T
  induction T with
  | zero =>
    intro k
    simp only [rightDist]
    split_ifs <;> norm_num
  | succ T ih =>
    intro k
    simp only [rightDist]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (ih j) (rightStep_nonneg n j k))

/-- The right-tree distribution has total mass one at every time. -/
lemma rightDist_sum (n : ℕ) : ∀ T : ℕ, ∑ k, rightDist n T k = 1 := by
  intro T
  induction T with
  | zero =>
    simp [rightDist]
  | succ T ih =>
    calc ∑ k, rightDist n (T + 1) k
        = ∑ k, ∑ j, rightDist n T j * rightStep n j k := by simp only [rightDist]
      _ = ∑ j, ∑ k, rightDist n T j * rightStep n j k := Finset.sum_comm
      _ = ∑ j, rightDist n T j * (∑ k, rightStep n j k) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.mul_sum]
      _ = ∑ j, rightDist n T j := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [rightStep_sum, mul_one]
      _ = 1 := ih

/-- For `n ≥ 1`, the expected barrier value remains equal to its initial value at every time. -/
lemma rightDist_expect (n : ℕ) (hn : 1 ≤ n) : ∀ T : ℕ,
    ∑ k, rightDist n T k * barrier n k = barrier n 0 := by
  intro T
  induction T with
  | zero =>
    simp only [rightDist]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | succ T ih =>
    calc ∑ k, rightDist n (T + 1) k * barrier n k
        = ∑ k, ∑ j, rightDist n T j * (rightStep n j k * barrier n k) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            simp only [rightDist]
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ j, ∑ k, rightDist n T j * (rightStep n j k * barrier n k) := Finset.sum_comm
      _ = ∑ j, rightDist n T j * (∑ k, rightStep n j k * barrier n k) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.mul_sum]
      _ = ∑ j, rightDist n T j * barrier n j := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [rightStep_expect, barrier_harmonic n hn]
      _ = barrier n 0 := ih

/-- For `n ≥ 1`, the mass at the root after any number of steps is at most `(1 / 2)^n`, as in
the classical propagation bound of [ChildsFarhiGutmann2002]. -/
theorem rightDist_root_le (n : ℕ) (hn : 1 ≤ n) (T : ℕ) :
    rightDist n T ⟨n, by omega⟩ ≤ (1 / 2 : ℝ) ^ n := by
  have hexp := rightDist_expect n hn T
  have hle : rightDist n T ⟨n, by omega⟩ * barrier n ⟨n, by omega⟩
      ≤ ∑ k, rightDist n T k * barrier n k :=
    Finset.single_le_sum (f := fun k => rightDist n T k * barrier n k)
      (fun k _ => mul_nonneg (rightDist_nonneg n T k) (barrier_nonneg n k))
      (Finset.mem_univ _)
  rw [hexp, show barrier n (⟨n, by omega⟩ : Fin (n + 2)) = 1 from bval_mid n, mul_one,
    show barrier n (0 : Fin (n + 2)) = (1 / 2 : ℝ) ^ n from bval_zero n] at hle
  exact hle

end Qatlib.Papers.QWalkDiff01.MainResults
