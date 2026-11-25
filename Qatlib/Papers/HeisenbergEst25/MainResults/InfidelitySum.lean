/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HeisenbergEst25.MainResults.Facts.PaperFact53
public import Qatlib.Papers.HeisenbergEst25.MainResults.Model.ProtocolModel
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Telescoping the finite infidelity sum

Lemma 4.3 reduces Eq. (24) by two telescoping sums. One difference comes
from consecutive windows of products, and the other from consecutive
values of the weight in Eq. (23). The source denominator is linear in
the resulting sum of products.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HeisenbergEst25.MainResults

open scoped BigOperators
open Qatlib.Papers.HeisenbergEst25.MainResults.Facts
open Qatlib.Papers.HeisenbergEst25.MainResults.Model

private noncomputable def window (k : ℕ) (L N : ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (N - i + j + 1) * (L - i + j + 1)

/-- Consecutive windows of length `k + 1` differ by a multiple of the shorter window. -/
private theorem window_step (k : ℕ) (L N : ℝ) (i : ℕ) :
    (L + N + (k : ℝ) + 1 - 2 * i) * window k L N i =
      (window (k + 1) L N i - window (k + 1) L N (i + 1)) / ((k : ℝ) + 1) := by
  rw [show L + N + (k : ℝ) + 1 - 2 * i = N - i + (L - i) + (k : ℝ) + 1 by ring]
  simpa only [window, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, one_div, div_eq_inv_mul, mul_one]
    using fact53_divided_product_telescoping k (N - i) (L - i)

/-- A window with positive length vanishes after the last term of the source sum. -/
private theorem window_end (k L N : ℕ) : window (k + 1) L N (L + 1) = 0 := by
  unfold window
  refine Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr (Nat.succ_pos k)) ?_
  simp [Nat.cast_add]

/-- The window starting at one factors into the first two offsets and the shorter initial window. -/
private theorem window_one (k : ℕ) (L N : ℝ) :
    window (k + 1) L N 1 = N * L * window k L N 0 := by
  unfold window
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_succ, Nat.cast_zero, zero_add, sub_zero,
    show N - 1 + 0 + 1 = N by ring, show L - 1 + 0 + 1 = L by ring]
  rw [mul_comm _ (N * L)]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => by ring)

/-- The two products indexed from one are the same window indexed from zero. -/
private theorem window_Icc (k : ℕ) (L N : ℝ) (i : ℕ) :
    (∏ j ∈ Finset.Icc 1 k, (N + j - i)) * (∏ j ∈ Finset.Icc 1 k, (L + j - i)) =
      window k L N i := by
  rw [← Finset.prod_mul_distrib]
  have h := Finset.prod_Ico_add'
    (fun j : ℕ => (N + j - i) * (L + j - i)) 0 k 1
  rw [← Finset.range_eq_Ico, Nat.zero_add, Finset.Ico_add_one_right_eq_Icc] at h
  rw [← h]
  exact Finset.prod_congr rfl (fun j _ => by push_cast; ring)

/-- An unweighted sum of consecutive differences telescopes. -/
private theorem sum_diff (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Summation by parts for the consecutive differences in the denominator. -/
private theorem weighted_diff (f w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), w i * (f i - f (i + 1))) =
      w 0 * f 0 + (∑ i ∈ Finset.range n, (w (i + 1) - w i) * f (i + 1)) -
        w n * f (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private noncomputable def prev (d L N i : ℕ) : ℝ :=
  if i = 0 then 0 else gCoeff d L N (i - 1)

/-- Consecutive weights in Eq. (23) differ by the linear factor in Eq. (24). -/
private theorem weight_delta (d L N i : ℕ) :
    gCoeff d L N i - prev d L N i = (L : ℝ) + N + d - 2 * i := by
  cases i with
  | zero => simp [prev, gCoeff]
  | succ i =>
    simp only [prev, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, gCoeff, Nat.cast_succ]
    ring

/-- Differencing the sum of two adjacent weights gives twice the next window factor. -/
private theorem weight_sum_delta (d L N i : ℕ) :
    (gCoeff d L N (i + 1) + prev d L N (i + 1)) -
        (gCoeff d L N i + prev d L N i) =
      2 * ((L : ℝ) + N + d + 1 - 2 * ((i + 1 : ℕ) : ℝ)) := by
  have hprev : prev d L N (i + 1) = gCoeff d L N i := by simp [prev]
  have hi := weight_delta d L N i
  have hj := weight_delta d L N (i + 1)
  rw [hprev] at hj ⊢
  push_cast at hj ⊢
  linarith

/-- A telescope at the next window length evaluates the change-of-weight term. -/
private theorem weight_tail (k L N : ℕ) :
    (∑ i ∈ Finset.range L,
      (2 * ((L : ℝ) + N + (k : ℝ) + 1 + 1 - 2 * ((i + 1 : ℕ) : ℝ))) *
        window (k + 1) L N (i + 1)) =
      (2 * (N : ℝ) * L * window (k + 1) L N 0) / ((k : ℝ) + 2) := by
  have hf (i : ℕ) :
      (2 * ((L : ℝ) + N + (k : ℝ) + 1 + 1 - 2 * ((i + 1 : ℕ) : ℝ))) *
          window (k + 1) L N (i + 1) =
        2 * (window (k + 1 + 1) L N (i + 1) - window (k + 1 + 1) L N (i + 1 + 1)) /
          ((k : ℝ) + 2) := by
    rw [mul_assoc, show (L : ℝ) + N + (k : ℝ) + 1 + 1 - 2 * ((i + 1 : ℕ) : ℝ) =
      (L : ℝ) + N + ((k + 1 : ℕ) : ℝ) + 1 - 2 * ((i + 1 : ℕ) : ℝ) by
        push_cast; ring, window_step]
    push_cast; ring
  simp_rw [hf]
  rw [← Finset.sum_div, ← Finset.mul_sum,
    sum_diff (fun i => window (k + 1 + 1) L N (i + 1)) L, window_end, sub_zero, window_one]
  ring

/-- For the prescribed weights, Eq. (24) equals the unsquared-denominator expression of Eq. (25). -/
theorem infidelity_sum (d L N : ℕ) (hd : 2 ≤ d) (hL : 0 < L) (hN : L ≤ N) :
    eq24 d L N (gCoeff d L N) =
      ((d : ℝ) - 1) / ((L : ℝ) + N + d + 2 / ((d : ℝ) + 1) * (N : ℝ) * L) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let gap (i : ℕ) : ℝ := (L : ℝ) + N + (k : ℝ) + 1 - 2 * i
  let w (i : ℕ) : ℝ := gCoeff (k + 1) L N i + prev (k + 1) L N i
  have hk : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hi : Finset.Icc (0 : ℕ) L = Finset.range (L + 1) := by
    ext i
    simp only [Finset.mem_Icc, Nat.zero_le, true_and, Finset.mem_range]
    omega
  have hΔ (i : ℕ) : gCoeff (k + 1) L N i - prev (k + 1) L N i = gap i := by
    simpa [gap, Nat.cast_succ, add_assoc] using weight_delta (k + 1) L N i
  have hg (i : ℕ) (hi : i ∈ Finset.range (L + 1)) : 0 < gap i := by
    have hi' : i ≤ L := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have h1 : (i : ℝ) ≤ L := by exact_mod_cast hi'
    have h2 : (L : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [gap]
    linarith
  have hnum :
      (∑ i ∈ Finset.range (L + 1), gap i * window k L N i) =
        window (k + 1) L N 0 / ((k : ℝ) + 1) := by
    simp_rw [show ∀ i, gap i * window k L N i =
      (window (k + 1) L N i - window (k + 1) L N (i + 1)) / ((k : ℝ) + 1) from
        window_step k L N]
    rw [← Finset.sum_div, sum_diff, window_end, sub_zero]
  have hden :
      (∑ i ∈ Finset.range (L + 1), w i * (gap i * window k L N i)) =
        ((L : ℝ) + N + (k : ℝ) + 1 + 2 / ((k : ℝ) + 2) * (N : ℝ) * L) *
          window (k + 1) L N 0 / ((k : ℝ) + 1) := by
    simp_rw [show ∀ i, gap i * window k L N i =
      (window (k + 1) L N i - window (k + 1) L N (i + 1)) / ((k : ℝ) + 1) from
        window_step k L N, ← mul_div_assoc]
    rw [← Finset.sum_div, weighted_diff, window_end, mul_zero, sub_zero]
    have hchange (i : ℕ) :
        w (i + 1) - w i =
          2 * ((L : ℝ) + N + (k : ℝ) + 1 + 1 - 2 * ((i + 1 : ℕ) : ℝ)) := by
      simpa only [w, Nat.cast_succ, add_assoc] using weight_sum_delta (k + 1) L N i
    simp_rw [hchange]
    rw [weight_tail]
    have hw : w 0 = (L : ℝ) + N + (k : ℝ) + 1 := by
      simp [w, prev, gCoeff, Nat.cast_succ, add_assoc]
    rw [hw]
    ring
  have hW : 0 < window (k + 1) L N 0 := by
    apply Finset.prod_pos
    intro j _
    simp only [Nat.cast_zero, sub_zero]
    positivity
  have hpositive : 0 < (L : ℝ) + N + (k : ℝ) + 1 + 2 / ((k : ℝ) + 2) * (N : ℝ) * L := by
    positivity
  unfold eq24
  change
    (∑ i ∈ Finset.Icc 0 L, ((gCoeff (k + 1) L N i - prev (k + 1) L N i) ^ 2 /
        ((L : ℝ) + N + ((k + 1 : ℕ) : ℝ) - 2 * i)) *
        (∏ j ∈ Finset.Icc 1 (k + 1 - 1), ((N : ℝ) + j - i)) *
        (∏ j ∈ Finset.Icc 1 (k + 1 - 1), ((L : ℝ) + j - i))) /
    (∑ i ∈ Finset.Icc 0 L, ((gCoeff (k + 1) L N i ^ 2 - prev (k + 1) L N i ^ 2) /
        (((k + 1 : ℕ) : ℝ) - 1)) *
        (∏ j ∈ Finset.Icc 1 (k + 1 - 1), ((N : ℝ) + j - i)) *
        (∏ j ∈ Finset.Icc 1 (k + 1 - 1), ((L : ℝ) + j - i))) = _
  simp only [hi, Nat.add_sub_cancel, Nat.cast_succ, add_sub_cancel_right, mul_assoc, window_Icc]
  have hNsum :
      (∑ i ∈ Finset.range (L + 1), (gCoeff (k + 1) L N i - prev (k + 1) L N i) ^ 2 /
        ((L : ℝ) + N + ((k : ℝ) + 1) - 2 * i) * window k L N i) =
      ∑ i ∈ Finset.range (L + 1), gap i * window k L N i := by
    apply Finset.sum_congr rfl
    intro i hi'
    rw [hΔ, show (L : ℝ) + N + ((k : ℝ) + 1) - 2 * i = gap i by simp [gap, add_assoc],
      sq, mul_div_cancel_right₀ _ (hg i hi').ne']
  have hDsum :
      (∑ i ∈ Finset.range (L + 1), (gCoeff (k + 1) L N i ^ 2 - prev (k + 1) L N i ^ 2) /
        (k : ℝ) * window k L N i) =
      (∑ i ∈ Finset.range (L + 1), w i * (gap i * window k L N i)) / (k : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have hx : gCoeff (k + 1) L N i ^ 2 - prev (k + 1) L N i ^ 2 = w i * gap i := by
      rw [← hΔ i]
      dsimp [w]
      ring
    rw [hx]
    ring
  rw [hNsum, hDsum, hnum, hden]
  have heq : (L : ℝ) + N + ((k : ℝ) + 1) + 2 / ((k : ℝ) + 1 + 1) * ((N : ℝ) * L) =
      (L : ℝ) + N + (k : ℝ) + 1 + 2 / ((k : ℝ) + 2) * (N : ℝ) * L := by ring_nf
  rw [heq]
  field_simp [hk.ne', hW.ne', hpositive.ne']

end Qatlib.Papers.HeisenbergEst25.MainResults
