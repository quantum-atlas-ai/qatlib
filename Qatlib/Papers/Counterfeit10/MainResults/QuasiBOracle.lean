/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# The quasi `B`-oracle (Counterfeit10, §3.3)

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Section 3.3 (Theorems 3 and 4, Lemma 5).

The *quasi* `B`-oracle first throws the `N` coins uniformly into the two pans and only then answers
the balance question of the resulting random weighing.  Consequently, when the `2N/c` pan coins
contain `m` false coins, the scale is

* balanced with probability `1` if `m = 0`,
* balanced with probability `1/√m` if `m` is even and positive,
* tilted with probability `1` (`m` odd), since two pans each holding an odd number of false coins
  cannot balance.

That is exactly the family of distributions to which the stochastic adversary theorem (Lemma 5)
applies, with `P_{ab,q}` the products of these probabilities.

This file records the oracle's answer distribution and its basic laws.  The stochastic adversary
theorem itself (Lemma 5) is a cited result and is not mechanised here; neither is the reduction
of the uniform pan assignment to these probabilities.
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- Probability that the quasi `B`-oracle answers "balanced" when the pan coins contain `m` false
coins: `1` for `m = 0`, `1/√m` for positive even `m`, and `0` for odd `m`. -/
noncomputable def quasiZeroProb (m : ℕ) : ℝ :=
  if m = 0 then 1 else if m % 2 = 0 then 1 / Real.sqrt (m : ℝ) else 0

/-- Probability that the quasi `B`-oracle answers "tilted" (`ζ = 1`), the complement of
`quasiZeroProb`. -/
noncomputable def quasiOneProb (m : ℕ) : ℝ := 1 - quasiZeroProb m

/-- With no false coin on the pans the scale is always balanced. -/
@[simp] lemma quasiZeroProb_zero : quasiZeroProb 0 = 1 := by
  unfold quasiZeroProb; simp

/-- With a positive even number of false coins the scale balances with probability `1/√m`. -/
lemma quasiZeroProb_even {m : ℕ} (hm : m ≠ 0) (he : m % 2 = 0) :
    quasiZeroProb m = 1 / Real.sqrt (m : ℝ) := by
  unfold quasiZeroProb; simp [hm, he]

/-- With an odd number of false coins the scale always tilts. -/
lemma quasiZeroProb_odd {m : ℕ} (hm : m ≠ 0) (ho : m % 2 ≠ 0) :
    quasiZeroProb m = 0 := by
  unfold quasiZeroProb; simp [hm, ho]

/-- The balanced probability is non-negative. -/
lemma quasiZeroProb_nonneg (m : ℕ) : 0 ≤ quasiZeroProb m := by
  unfold quasiZeroProb
  split_ifs
  · norm_num
  · exact div_nonneg zero_le_one (Real.sqrt_nonneg (m : ℝ))
  · exact le_refl 0

/-- The tilted probability is non-negative. -/
lemma quasiOneProb_nonneg {m : ℕ} (h : quasiZeroProb m ≤ 1) : 0 ≤ quasiOneProb m := by
  unfold quasiOneProb; linarith

/-- The two answers are complementary. -/
lemma quasi_probs_sum (m : ℕ) : quasiZeroProb m + quasiOneProb m = 1 := by
  unfold quasiOneProb; ring

/-- For an odd number of pan coins the quasi `B`-oracle answers "tilted" with certainty, which is
the degenerate distribution used in Lemma 5. -/
lemma quasiOneProb_eq_one_of_odd {m : ℕ} (hm : m ≠ 0) (ho : m % 2 ≠ 0) :
    quasiOneProb m = 1 := by
  unfold quasiOneProb; rw [quasiZeroProb_odd hm ho]; ring

/-- The tilted probability is at most `1`. -/
lemma quasiOneProb_le_one {m : ℕ} (h : 0 ≤ quasiZeroProb m) : quasiOneProb m ≤ 1 := by
  unfold quasiOneProb; linarith

end Qatlib.Papers.Counterfeit10.MainResults
