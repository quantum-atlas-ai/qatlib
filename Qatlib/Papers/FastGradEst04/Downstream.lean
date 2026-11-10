/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastGradEst04.Downstream

def localEnergy (a b c : ℝ) : ℝ := (1 / 2) * ((b - a) ^ 2 + (c - b) ^ 2)

theorem localEnergy_completion (a b c : ℝ) :
    localEnergy a b c = (b - (a + c) / 2) ^ 2 + (a - c) ^ 2 / 4 := by
  unfold localEnergy
  ring

theorem localEnergy_ge (a b c : ℝ) : localEnergy a b c ≥ (a - c) ^ 2 / 4 := by
  rw [localEnergy_completion]
  nlinarith [sq_nonneg (b - (a + c) / 2)]

theorem localEnergy_eq_iff (a b c : ℝ) :
    localEnergy a b c = (a - c) ^ 2 / 4 ↔ 2 * b = a + c := by
  rw [localEnergy_completion]
  constructor
  · intro h
    have hsq : (b - (a + c) / 2) ^ 2 = 0 := by linarith
    have hb : b = (a + c) / 2 := by nlinarith [sq_nonneg (b - (a + c) / 2)]
    linarith
  · intro h
    have hb : b = (a + c) / 2 := by linarith
    rw [hb]
    ring

theorem error_accumulation (e : ℕ → ℝ) (ρ ε : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hε : 0 ≤ ε) (h0 : 0 ≤ e 0) (hrec : ∀ k, e (k + 1) ≤ ρ * e k + ε) :
    ∀ k, e k ≤ e 0 + ε * k := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    have hbase : 0 ≤ e 0 + ε * n := by positivity
    have hstep : e (n + 1) ≤ ρ * e n + ε := hrec n
    have hmul : ρ * e n ≤ ρ * (e 0 + ε * n) := mul_le_mul_of_nonneg_left ih hρ0
    have hcontr : ρ * (e 0 + ε * n) ≤ 1 * (e 0 + ε * n) :=
      mul_le_mul_of_nonneg_right hρ1 hbase
    push_cast
    nlinarith [hstep, hmul, hcontr]

end Qatlib.Papers.FastGradEst04.Downstream
