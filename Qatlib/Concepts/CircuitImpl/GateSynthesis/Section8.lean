/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Section 8 dimension-count arithmetic

This module formalizes numerical parameter-count calculations associated with Section 8 of
[BarencoEtAl1995]. The functions `dimU` and `dimSU` are the counts `4 ^ n` and `4 ^ n - 1`; the
results check the increments and totals used in the three-qubit calculation.

It also defines the rational threshold `omega` and proves an arithmetic bound for the Gray-path
transport expression.

## Main statements

* `second_gate_increment` and `third_gate_increment`: the numerical increments 12 and 9 and
  their cumulative totals.
* `sixth_gate_reaches_U8`: the cumulative expression equals the three-qubit unitary parameter
  count.
* `omega_three`: the threshold at three qubits is six.
* `gray_transport_gate_bound`: the transport expression is bounded under `m ≤ n + 1`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis.Section8

/-- The numerical unitary parameter count `4 ^ n` for an `n`-qubit system. -/
def dimU (n : ℕ) : ℕ := 4 ^ n

/-- The numerical special-unitary parameter count `4 ^ n - 1` for an `n`-qubit system. -/
def dimSU (n : ℕ) : ℕ := 4 ^ n - 1

/-- The unitary parameter count at two qubits is 16. -/
theorem dimU_two : dimU 2 = 16 := by norm_num [dimU]

/-- The unitary parameter count at three qubits is 64. -/
theorem dimU_three : dimU 3 = 64 := by norm_num [dimU]

/-- The special-unitary parameter count at two qubits is 15. -/
theorem dimSU_two : dimSU 2 = 15 := by norm_num [dimSU]

/-- The special-unitary parameter count at one qubit is three. -/
theorem dimSU_one : dimSU 1 = 3 := by norm_num [dimSU]

/-- The difference `dimSU 2 - dimSU 1` is 12, and adding this increment to `dimU 2` gives 28. -/
theorem second_gate_increment :
    dimSU 2 - dimSU 1 = 12 ∧ dimU 2 + 12 = 28 := by
  constructor <;> norm_num [dimU, dimSU]

/-- The expression `dimU 2 - 1 - dimSU 1 - dimSU 1` is nine, and the cumulative total `dimU 2 +
12 + 9` is 37. -/
theorem third_gate_increment :
    dimU 2 - 1 - dimSU 1 - dimSU 1 = 9 ∧ dimU 2 + 12 + 9 = 37 := by
  constructor <;> norm_num [dimU, dimSU]

/-- The numerical total `dimU 2 + 12 + 9 + 9 * 3` equals the three-qubit unitary parameter
count. -/
theorem sixth_gate_reaches_U8 :
    dimU 2 + 12 + 9 + 9 * 3 = dimU 3 := by
  norm_num [dimU]

/-- The rational threshold `4 ^ n / 9 - n / 3 - 1 / 9`. -/
def omega (n : ℕ) : ℚ := (4 : ℚ) ^ n / 9 - n / 3 - 1 / 9

/-- The rational threshold `omega` evaluates to six at three qubits. -/
theorem omega_three : omega 3 = 6 := by
  unfold omega
  norm_num

/-- If `m ≤ n + 1`, then `2 * m - 3 ≤ 2 * n - 1` with natural-number subtraction. -/
theorem gray_transport_gate_bound (n m : ℕ) (hm : m ≤ n + 1) :
    2 * m - 3 ≤ 2 * n - 1 := by
  omega

end Qatlib.Concepts.CircuitImpl.GateSynthesis.Section8
