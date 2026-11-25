/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs

@[expose] public section

/-!
# From a dimension count to the gate-count lower bound of Theorem 3.4

A word of `b` two-input gates has at most `9 * b + 3 * n + 1` real parameters, while the space of
`k`-frames in dimension `2 ^ n` has dimension `k * (2 ^ (n + 1) - k)`. Whenever the parameter count
reaches the frame dimension, the number of gates satisfies the lower bound
`(k / 9) * (2 ^ (n + 1) - k) - n / 3 - 1 / 9` of [Knill1995], Theorem 3.4.

This module proves only that arithmetic bridge. It does not prove the parameter count itself: the
manifold dimension of the gate image, the zero-measure argument of Lemmas 3.5-3.7, and the global
gauge accounting that turns equality into a covering statement remain open. The domain restriction
`k ≤ 2 ^ n` is the one used by the paper.

## Main statements

* `b_two_n_k_lower_of_dim`: the dimension count implies the displayed lower bound on `b`.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCircApprox95.MainResults

/-- If the parameter count `9 * b + 3 * n + 1` of a `b`-gate word reaches the dimension
`k * (2 ^ (n + 1) - k)` of the `k`-frame space, then `b` is at least
`(k / 9) * (2 ^ (n + 1) - k) - n / 3 - 1 / 9` [Knill1995], Theorem 3.4. The hypothesis `k ≤ 2 ^ n`
is the paper's frame range and identifies the natural-number difference `2 ^ (n + 1) - k` with the
corresponding real difference. This is the arithmetic reduction only; the parameter count of a gate
word, the manifold dimension of its image and the zero-measure argument are not proved here. -/
theorem b_two_n_k_lower_of_dim {n k b : ℕ} (hk : k ≤ 2 ^ n)
    (hdim : k * (2 ^ (n + 1) - k) ≤ 9 * b + 3 * n + 1) :
    ((k : ℝ) / 9) * ((2 : ℝ) ^ (n + 1) - (k : ℝ)) - (n : ℝ) / 3 - 1 / 9 ≤ (b : ℝ) := by
  have hk2 : k ≤ 2 ^ (n + 1) :=
    le_trans hk (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  have hcast : ((k * (2 ^ (n + 1) - k) : ℕ) : ℝ) =
      (k : ℝ) * ((2 : ℝ) ^ (n + 1) - (k : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hk2]
    push_cast
    ring
  have hR : (k : ℝ) * ((2 : ℝ) ^ (n + 1) - (k : ℝ)) ≤ 9 * (b : ℝ) + 3 * (n : ℝ) + 1 := by
    have h : ((k * (2 ^ (n + 1) - k) : ℕ) : ℝ) ≤ ((9 * b + 3 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdim
    rw [hcast] at h
    push_cast at h
    linarith [h]
  nlinarith [hR]

end Qatlib.Papers.QCircApprox95.MainResults
