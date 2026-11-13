/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversarySrch07.MainResults.XiSequence.XiBasic
import Mathlib.RingTheory.Binomial

/-!
# Convolution identity for the ordered-search sequence

Relates the sequence `xi` to generalized binomial coefficients at −1/2 and proves its
self-convolution identity. This is the sequence identity used in the ordered-search adversary
construction. See [ChildsLee2008].

## Main statements

* `ringChoose_neg_half`: expresses generalized binomial coefficients in terms of `xi`.
* `source_proposition_four`: the convolution of `xi` with itself equals one at every index.

## References

* [Childs and Lee, 2008][ChildsLee2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Finset

namespace Qatlib.Papers.AdversarySrch07.MainResults.XiSequence

open Qatlib.Papers.AdversarySrch07.MainResults

/-- The generalized binomial coefficient at −1/2 equals `(-1)^n * xi n`. -/
theorem ringChoose_neg_half (n : ℕ) :
    Ring.choose (-(1 / 2) : ℝ) n = (-1 : ℝ) ^ n * xi n := by
  induction n with
  | zero => simp [xi]
  | succ n ih =>
    have hrec := Ring.choose_smul_choose (-(1 / 2) : ℝ) (n := n + 1) (k := n) (Nat.le_succ n)
    rw [Nat.choose_succ_self_right, show n + 1 - n = 1 from by omega,
      Ring.choose_one_right, nsmul_eq_mul] at hrec
    push_cast at hrec
    rw [ih, show (-(1 / 2) : ℝ) - (n : ℝ) = -((n : ℝ) + 1 / 2) by ring] at hrec
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hkey : ((n : ℝ) + 1) * Ring.choose (-(1 / 2) : ℝ) (n + 1) =
        ((n : ℝ) + 1) * ((-1 : ℝ) ^ (n + 1) * xi (n + 1)) := by
      rw [hrec, pow_succ, xi_succ_ratio]
      field_simp
    exact mul_left_cancel₀ hn hkey

/-- The generalized binomial coefficient at −1 equals `(-1)^j`. -/
theorem ringChoose_neg_one (j : ℕ) : Ring.choose (-1 : ℝ) j = (-1 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hrec := Ring.choose_smul_choose (-1 : ℝ) (n := n + 1) (k := n) (Nat.le_succ n)
    rw [Nat.choose_succ_self_right, show n + 1 - n = 1 from by omega,
      Ring.choose_one_right, nsmul_eq_mul,
      show (-1 : ℝ) - (n : ℝ) = -((n : ℝ) + 1) by ring, ih] at hrec
    push_cast at hrec
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hkey : ((n : ℝ) + 1) * Ring.choose (-1 : ℝ) (n + 1) =
        ((n : ℝ) + 1) * (-1 : ℝ) ^ (n + 1) := by
      rw [hrec, pow_succ]
      ring
    exact mul_left_cancel₀ hn hkey

/-- For every natural number `j`, the sum of `xi i * xi (j - i)` over `0 ≤ i ≤ j` equals one
[Childs and Lee, Proposition 4][ChildsLee2008]. -/
theorem source_proposition_four (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), xi i * xi (j - i) = 1 := by
  have hv := Ring.add_choose_eq (r := (-(1 / 2) : ℝ)) (s := (-(1 / 2) : ℝ)) j (Commute.all _ _)
  rw [show (-(1 / 2) : ℝ) + (-(1 / 2) : ℝ) = -1 by ring, ringChoose_neg_one] at hv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => Ring.choose (-(1 / 2) : ℝ) a * Ring.choose (-(1 / 2) : ℝ) b)] at hv
  simp_rw [ringChoose_neg_half] at hv
  have hfact : ∀ k ∈ Finset.range (j + 1),
      ((-1 : ℝ) ^ k * xi k) * ((-1 : ℝ) ^ (j - k) * xi (j - k))
        = (-1 : ℝ) ^ j * (xi k * xi (j - k)) := by
    intro k hk
    have hkj : k ≤ j := Finset.mem_range_succ_iff.mp hk
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (j - k) = (-1 : ℝ) ^ j := by
      rw [← pow_add, Nat.add_sub_cancel' hkj]
    calc ((-1 : ℝ) ^ k * xi k) * ((-1 : ℝ) ^ (j - k) * xi (j - k))
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (j - k)) * (xi k * xi (j - k)) := by ring
      _ = (-1 : ℝ) ^ j * (xi k * xi (j - k)) := by rw [hsign]
  have hsum :
      ∑ k ∈ Finset.range (j + 1), ((-1 : ℝ) ^ k * xi k) * ((-1 : ℝ) ^ (j - k) * xi (j - k))
        = (-1 : ℝ) ^ j * ∑ k ∈ Finset.range (j + 1), xi k * xi (j - k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hfact
  rw [hsum] at hv
  have hv' : (-1 : ℝ) ^ j * ∑ k ∈ Finset.range (j + 1), xi k * xi (j - k) =
      (-1 : ℝ) ^ j * 1 := by
    rw [mul_one]
    exact hv.symm
  exact mul_left_cancel₀ (pow_ne_zero j (by norm_num : (-1 : ℝ) ≠ 0)) hv'

end Qatlib.Papers.AdversarySrch07.MainResults.XiSequence
