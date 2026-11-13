/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsExt
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elliptic curve resource formulas

`qubitCount`, `pointAddToffoli`, and `shorToffoli` record the scalar resource expressions for
elliptic curve discrete logarithm circuits. The module evaluates the qubit expression at width
256 and proves how basic gate counts, peak live qubits, and depth behave when a resource account
is repeated `2 * n` times.

The mathematical setting follows [RoettelerEtAl2017].

## Main statements

* `qubitCount_P256`: the width 256 qubit expression equals 2330.
* `shorToffoli_eq_two_n_mul_pointAddToffoli`: the total expression is `2 * n` times the point
  addition expression.
* `shor_toffoli_via_repeat`: transfer of a point addition gate bound to the repeated account.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.ResourceDefs

open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs

/-- The qubit count expression `9 * n + 2 * Nat.clog 2 n + 10`. -/
def qubitCount (n : ℕ) : ℕ := 9 * n + 2 * Nat.clog 2 n + 10

/-- The binary ceiling logarithm of a natural number is at most that number. -/
theorem clog_two_le_self {n : ℕ} : Nat.clog 2 n ≤ n := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact Nat.le_of_lt Nat.lt_two_pow_self

/-- The qubit count expression is at most `9 * n + 2 * n + 10`. -/
theorem qubitCount_le_linear (n : ℕ) :
    qubitCount n ≤ 9 * n + 2 * n + 10 := by
  unfold qubitCount
  have h := clog_two_le_self (n := n)
  omega

/-- The qubit count expression at width 256 equals 2330. See [Roetteler et al., 2017, Fig11 /
Table2: simulated circuits, fits and NIST benchmarks][RoettelerEtAl2017]. -/
theorem qubitCount_P256 : qubitCount 256 = 2330 := by
  unfold qubitCount
  have hlog : Nat.clog 2 256 = 8 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.clog_pow _ _ (by norm_num)]
  rw [hlog]

/-- The point addition Toffoli expression `224 * n² * L + 2045 * n²`, with logarithmic parameter
`L`. -/
noncomputable def pointAddToffoli (n : ℕ) (L : ℝ) : ℝ :=
  224 * (n : ℝ) ^ 2 * L + 2045 * (n : ℝ) ^ 2

/-- The total Toffoli expression `448 * n³ * L + 4090 * n³`, with logarithmic parameter `L`. -/
noncomputable def shorToffoli (n : ℕ) (L : ℝ) : ℝ :=
  448 * (n : ℝ) ^ 3 * L + 4090 * (n : ℝ) ^ 3

/-- Multiplying the point addition Toffoli expression by `2 * n` gives the total Toffoli
expression. See [Roetteler et al., 2017, Abstract / Results: complete ECDLP resource
estimate][RoettelerEtAl2017]. -/
theorem shorToffoli_eq_two_n_mul_pointAddToffoli (n : ℕ) (L : ℝ) :
    (2 * (n : ℝ)) * pointAddToffoli n L = shorToffoli n L := by
  unfold pointAddToffoli shorToffoli
  ring

/-- Repeating an account `2 * n` times multiplies its basic gate count by `2 * n`. -/
theorem repeat_basicGates_two_n (pa : Account) (n : ℕ) :
    (Account.repeat pa (2 * n)).basicGates = (2 * n) * pa.basicGates :=
  repeat_basicGates pa (2 * n)

/-- The peak live resource of a repeated account is at most that of the original account. -/
theorem repeat_livePeak_le (a : Account) (k : ℕ) :
    (Account.repeat a k).livePeak ≤ a.livePeak := by
  induction k with
  | zero => simp [Account.repeat, Account.zero]
  | succ k ih =>
      show (Account.seq a (Account.repeat a k)).livePeak ≤ a.livePeak
      rw [seq_livePeak]
      exact max_le le_rfl ih

/-- Repeating the point addition account `2 * n` times does not exceed its original peak live
resource. -/
theorem shor_qubits_reuse (pa : Account) (n : ℕ) :
    (Account.repeat pa (2 * n)).livePeak ≤ pa.livePeak :=
  repeat_livePeak_le pa (2 * n)

/-- Repeating the point addition account `2 * n` times multiplies its depth by `2 * n`. -/
theorem shor_depth_repeat (pa : Account) (n : ℕ) :
    (Account.repeat pa (2 * n)).depth = (2 * n) * pa.depth :=
  repeat_depth pa (2 * n)

/-- A basic gate bound by `pointAddToffoli` yields a bound by `shorToffoli` for the account
repeated `2 * n` times. See [Roetteler et al., 2017, Abstract / Results: complete ECDLP
resource estimate][RoettelerEtAl2017]. -/
theorem shor_toffoli_via_repeat (n : ℕ) (pa : Account) (L : ℝ)
    (hpa : (pa.basicGates : ℝ) ≤ pointAddToffoli n L) :
    ((Account.repeat pa (2 * n)).basicGates : ℝ) ≤ shorToffoli n L := by
  rw [repeat_basicGates]
  have hcast :
      (((2 * n) * pa.basicGates : ℕ) : ℝ) = (2 * (n : ℝ)) * (pa.basicGates : ℝ) := by
    push_cast
    ring
  rw [hcast]
  calc
    (2 * (n : ℝ)) * (pa.basicGates : ℝ)
        ≤ (2 * (n : ℝ)) * pointAddToffoli n L := by
          exact mul_le_mul_of_nonneg_left hpa (by positivity)
    _ = shorToffoli n L := shorToffoli_eq_two_n_mul_pointAddToffoli n L

end Qatlib.Papers.ECDLPResource17.ResourceDefs
