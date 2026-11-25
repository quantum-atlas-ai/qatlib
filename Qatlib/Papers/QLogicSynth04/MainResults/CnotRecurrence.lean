/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Unrolling the Shannon decomposition cost inequality

Equation (17) gives a four-way recurrence for the CNOT count. Equation (18)
bounds its solution from any chosen base case.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLogicSynth04.MainResults

/-- The four-way recurrence implies Eq. (18) from any fixed base level. -/
theorem recurrence_le (c : ℕ → ℝ) (ℓ : ℕ)
    (hrec : ∀ j, ℓ < j → c j ≤ 4 * c (j - 1) + 3 * (2 : ℝ) ^ (j - 1)) :
    ∀ n, ℓ ≤ n →
      c n ≤ (4 : ℝ) ^ (n - ℓ) * (c ℓ + 3 * (2 : ℝ) ^ (ℓ - 1)) -
        3 * (2 : ℝ) ^ (n - 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hstep := hrec (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    have hpow : (2 : ℝ) ^ n ≤ 2 * (2 : ℝ) ^ (n - 1) := by
      cases n with
      | zero => norm_num
      | succ n => rw [Nat.succ_sub_one, pow_succ, mul_comm]
    have hsub : n + 1 - ℓ = n - ℓ + 1 := by omega
    rw [hsub, pow_succ, Nat.add_sub_cancel]
    linarith [mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 4 by norm_num)]

end Qatlib.Papers.QLogicSynth04.MainResults
