/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Mathlib.Data.Nat.Log
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GraphIsom13.CostLedger

open Qatlib.Papers.GraphIsom13.GiCost

def numQubits (N : ℕ) : ℕ := N * encBits N

def termCount1 (N : ℕ) : ℕ := N * (encSize N - N)

def termCount2 (N : ℕ) : ℕ := N * (N - 1) / 2

def termCount3 (N : ℕ) : ℕ := N ^ 2

def termCount (N : ℕ) : ℕ := termCount1 N + termCount2 N + termCount3 N

theorem encSize_lt_two_mul {N : ℕ} (hN : 2 ≤ N) : encSize N < 2 * N := by
  have hN1 : 1 < N := by omega
  have hU : 0 < encBits N := Nat.clog_pos (by norm_num) hN1
  have hpow := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
  unfold encSize
  have hsucc : (encBits N).pred.succ = encBits N := Nat.succ_pred_eq_of_pos hU
  have h2 : 2 ^ encBits N = 2 * 2 ^ (encBits N).pred := by
    conv_lhs => rw [← hsucc]
    rw [pow_succ, Nat.mul_comm]
  rw [h2]
  exact Nat.mul_lt_mul_of_pos_left hpow (by norm_num)

theorem termCount1_lt {N : ℕ} (hN : 2 ≤ N) : termCount1 N < 2 * N ^ 2 := by
  have hlt := encSize_lt_two_mul hN
  unfold termCount1
  calc N * (encSize N - N) ≤ N * encSize N := Nat.mul_le_mul_left N (Nat.sub_le _ _)
    _ < N * (2 * N) := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    _ = 2 * N ^ 2 := by ring

theorem termCount2_le (N : ℕ) : termCount2 N ≤ N ^ 2 := by
  unfold termCount2
  calc N * (N - 1) / 2 ≤ N * (N - 1) := Nat.div_le_self _ _
    _ ≤ N * N := Nat.mul_le_mul_left N (Nat.sub_le _ _)
    _ = N ^ 2 := by ring

theorem termCount_quadratic {N : ℕ} (hN : 2 ≤ N) :
    termCount N ≤ 4 * numQubits N ^ 2 := by
  have hN1 : 1 < N := by omega
  have hU : 0 < encBits N := Nat.clog_pos (by norm_num) hN1
  have hNle : N ≤ numQubits N := by
    unfold numQubits
    calc N = N * 1 := by ring
      _ ≤ N * encBits N := Nat.mul_le_mul_left N hU
  have hsq : N ^ 2 ≤ numQubits N ^ 2 := Nat.pow_le_pow_left hNle 2
  have h1 : termCount1 N ≤ 2 * N ^ 2 := le_of_lt (termCount1_lt hN)
  have h2 : termCount2 N ≤ N ^ 2 := termCount2_le N
  have h3 : termCount3 N ≤ N ^ 2 := le_of_eq rfl
  unfold termCount
  calc termCount1 N + termCount2 N + termCount3 N
      ≤ 2 * N ^ 2 + N ^ 2 + N ^ 2 := Nat.add_le_add (Nat.add_le_add h1 h2) h3
    _ = 4 * N ^ 2 := by ring
    _ ≤ 4 * numQubits N ^ 2 := Nat.mul_le_mul_left 4 hsq

theorem cost_component_budget {N : ℕ} (hN : 2 ≤ N) :
    numQubits N + termCount N ≤ 5 * numQubits N ^ 2 := by
  have hN1 : 1 < N := by omega
  have hU : 0 < encBits N := Nat.clog_pos (by norm_num) hN1
  have hL : 1 ≤ numQubits N := by
    unfold numQubits
    calc 1 ≤ N := by omega
      _ = N * 1 := by ring
      _ ≤ N * encBits N := Nat.mul_le_mul_left N hU
  have hT := termCount_quadratic hN
  have hLs : numQubits N ≤ numQubits N ^ 2 := by
    calc numQubits N = numQubits N * 1 := by ring
      _ ≤ numQubits N * numQubits N := Nat.mul_le_mul_left _ hL
      _ = numQubits N ^ 2 := by ring
  calc numQubits N + termCount N
      ≤ numQubits N ^ 2 + 4 * numQubits N ^ 2 := Nat.add_le_add hLs hT
    _ = 5 * numQubits N ^ 2 := by ring

end Qatlib.Papers.GraphIsom13.CostLedger
