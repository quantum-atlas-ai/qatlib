/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.CharacterSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Random code phase states and proposed time expressions

This module proves orthogonality of distinct codeword phase states over `ZMod A` and bounds
`printedCollisionExpr` by a union-bound expression. It records the proposed random-code time
formulas from [TerhalSmolin1998] and an arithmetic condition under which the quantum expression
is no larger than the classical one.

## Main statements

* `printedCollisionExpr_le`: For positive alphabet size, the printed collision expression is at
  most `(k - 1) / A^m`.
* `proposedRandomTime_comparison`: If `2 ≤ m` and `m * n + 2 ≤ (m - 1) * T`, the proposed
  random-code quantum time is at most the proposed classical time.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option warningAsError false

namespace Qatlib.Papers.SingleQuery97.MainResults.RandomCoding

open Qatlib.Papers.SingleQuery97.MainResults.CharacterSum

/-- The phase-state amplitude associated with a codeword over `ZMod A`. -/
noncomputable def randomState {A m : ℕ} [NeZero A] (z : Fin m → ZMod A) :
    (Fin m → ZMod A) → ℂ :=
  stateAmp z

/-- The inner product of two random-code phase states is `1` for equal codewords and `0` for
distinct codewords. -/
theorem randomStates_orthonormal {A m : ℕ} [NeZero A] (hA : 0 < A)
    (z z' : Fin m → ZMod A) :
    inner (randomState z) (randomState z') = if z = z' then 1 else 0 :=
  inner_stateAmp hA z z'

/-- Two random-code phase states have nonzero inner product exactly when their codewords are
equal. -/
theorem random_nonorthogonal_iff_code_equal {A m : ℕ} [NeZero A] (hA : 0 < A)
    (z z' : Fin m → ZMod A) :
    inner (randomState z) (randomState z') ≠ 0 ↔ z = z' := by
  rw [randomStates_orthonormal hA]
  by_cases h : z = z' <;> simp [h]

/-- The real expression `1 - (1 - (A^m)⁻¹)^(k - 1)` printed for the collision probability. -/
noncomputable def printedCollisionExpr (A m k : ℕ) : ℝ :=
  1 - (1 - ((A : ℝ) ^ m)⁻¹) ^ (k - 1)

/-- For `0 ≤ x ≤ 1`, the expression `1 - (1 - x)^n` is at most `n * x`. -/
theorem one_sub_pow_le_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ n : ℕ, 1 - (1 - x) ^ n ≤ (n : ℝ) * x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hbase : 0 ≤ 1 - x := by linarith
      have hle1 : (1 - x) ^ n ≤ 1 :=
        pow_le_one₀ hbase (by linarith)
      have hmul : (1 - x) ^ n * x ≤ 1 * x :=
        mul_le_mul_of_nonneg_right hle1 hx
      calc
        1 - (1 - x) ^ (n + 1) = (1 - (1 - x) ^ n) + (1 - x) ^ n * x := by
          rw [pow_succ]
          ring
        _ ≤ (n : ℝ) * x + 1 * x := by linarith
        _ = ((n + 1 : ℕ) : ℝ) * x := by
          push_cast
          ring

/-- For positive alphabet size, the printed collision expression is at most `(k - 1) / A^m`. -/
theorem printedCollisionExpr_le (A m k : ℕ) (hA : 0 < A) :
    printedCollisionExpr A m k ≤ ((k - 1 : ℕ) : ℝ) * ((A : ℝ) ^ m)⁻¹ := by
  unfold printedCollisionExpr
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hx : 0 ≤ ((A : ℝ) ^ m)⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos hA' m))
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hA
  have hx1 : ((A : ℝ) ^ m)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hA1)
  simpa using one_sub_pow_le_mul hx hx1 (k - 1)

/-- The proposed random-code quantum time expression `2 + m * n + T`. -/
def proposedRandomQuantumTime (n m T : ℕ) : ℕ := 2 + m * n + T

/-- The proposed random-code classical time expression `m / 2 + m * T`, with natural-number
division. -/
def proposedRandomClassicalTime (m T : ℕ) : ℕ := m / 2 + m * T

/-- If `2 ≤ m` and `m * n + 2 ≤ (m - 1) * T`, the proposed random-code quantum time is at most
the proposed classical time. -/
theorem proposedRandomTime_comparison {n m T : ℕ} (hm : 2 ≤ m)
    (hT : m * n + 2 ≤ (m - 1) * T) :
    proposedRandomQuantumTime n m T ≤ proposedRandomClassicalTime m T := by
  unfold proposedRandomQuantumTime proposedRandomClassicalTime
  have hm1 : 1 ≤ m := by omega
  have hmul : (m - 1) * T + T = m * T := by
    have h : (m - 1) * T + 1 * T = m * T := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hm1]
    simpa using h
  rw [← hmul]
  omega

end Qatlib.Papers.SingleQuery97.MainResults.RandomCoding
