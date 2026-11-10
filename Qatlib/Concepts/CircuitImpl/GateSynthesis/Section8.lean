/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis.Section8

def dimU (n : ℕ) : ℕ := 4 ^ n

def dimSU (n : ℕ) : ℕ := 4 ^ n - 1

theorem dimU_two : dimU 2 = 16 := by norm_num [dimU]

theorem dimU_three : dimU 3 = 64 := by norm_num [dimU]

theorem dimSU_two : dimSU 2 = 15 := by norm_num [dimSU]

theorem dimSU_one : dimSU 1 = 3 := by norm_num [dimSU]

theorem second_gate_increment :
    dimSU 2 - dimSU 1 = 12 ∧ dimU 2 + 12 = 28 := by
  constructor <;> norm_num [dimU, dimSU]

theorem third_gate_increment :
    dimU 2 - 1 - dimSU 1 - dimSU 1 = 9 ∧ dimU 2 + 12 + 9 = 37 := by
  constructor <;> norm_num [dimU, dimSU]

theorem sixth_gate_reaches_U8 :
    dimU 2 + 12 + 9 + 9 * 3 = dimU 3 := by
  norm_num [dimU]

def omega (n : ℕ) : ℚ := (4 : ℚ) ^ n / 9 - n / 3 - 1 / 9

theorem omega_three : omega 3 = 6 := by
  unfold omega
  norm_num

theorem gray_transport_gate_bound (n m : ℕ) (hm : m ≤ n + 1) :
    2 * m - 3 ≤ 2 * n - 1 := by
  omega

end Qatlib.Concepts.CircuitImpl.GateSynthesis.Section8
