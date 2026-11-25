/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BettiNumber25.MainResults.PowerSandwich

@[expose] public section

/-!
# Polynomial retries for the many-solutions construction

The probability argument following Eq. (13) boosts an inverse-polynomial
one-trial success bound by independent randomization. The failure product
at the lower success probability decays exponentially in the number of
trials divided by the polynomial.
-/

set_option autoImplicit false

open Qatlib.Papers.BettiNumber25.MainResults.PowerSandwich

namespace Qatlib.Papers.AdiabGaps09.MainResults

/-- Twice the polynomial denominator suffices for independent repetitions
of an experiment whose one-trial success probability is at least its inverse. -/
theorem polynomial_retries_bounded (k c : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℕ, 0 < K ∧ K ≤ 2 * k ^ c ∧
      (1 : ℝ) / 2 ≤ 1 - (1 - 1 / ((k : ℝ) ^ c)) ^ K := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (1 : ℝ) ≤ (k : ℝ) ^ c := one_le_pow₀ hkR
  have hpos : 0 < (k : ℝ) ^ c := zero_lt_one.trans_le hpow
  let K := 2 * k ^ c
  have hK : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos (by decide) (Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_one hk))
  have hmul : 1 / ((k : ℝ) ^ c) * (K : ℝ) = 2 := by
    dsimp [K]
    push_cast
    field_simp [ne_of_gt hpos]
  have htail := one_sub_pow_le_exp (1 / ((k : ℝ) ^ c))
    (one_div_pos.mpr hpos) ((div_le_one hpos).2 hpow) K
  rw [hmul] at htail
  have hexp : (2 : ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hhalf : Real.exp (-2) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp
  refine ⟨K, hK, le_rfl, ?_⟩
  linarith [htail.trans hhalf]

end Qatlib.Papers.AdiabGaps09.MainResults
