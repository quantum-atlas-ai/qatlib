/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumPCA14.InputAccess.IndexedColumnLoad
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCA14.InputAccess

open Matrix
open scoped ComplexOrder

open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix)
open Qatlib.Concepts.CopyEvolution.Discriminate (copyPrecisionBudget)

def qramDepth (d : ℕ) : ℕ := addressBits d

private theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc k + 1 + 1 = (k + 1) + 1 := rfl
      _ ≤ 2 ^ k + 1 := by omega
      _ ≤ 2 ^ k + 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

theorem addressBits_lt_self {m : ℕ} (hm : 0 < m) : addressBits m < m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : addressBits (k + 1) ≤ k := by
    rw [addressBits, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
    simpa using succ_le_two_pow k
  omega

theorem addressBits_le_self (m : ℕ) : addressBits m ≤ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [addressBits]
  · exact (addressBits_lt_self h).le

def swapGateCount (d : ℕ) : ℕ := 3 * qramDepth d

def stepGateCount (d : ℕ) : ℕ := swapGateCount d + 1

def copyProtocolGateCount (n d : ℕ) : ℕ := n * stepGateCount d

theorem stepGateCount_lt_naive {d : ℕ} (hd : 0 < d) :
    stepGateCount d < 3 * d + 1 := by
  have h1 : qramDepth d < d := addressBits_lt_self hd
  unfold stepGateCount swapGateCount
  omega

theorem copyProtocolGateCount_le_dlogd {n d : ℕ} (hnd : n ≤ d) :
    copyProtocolGateCount n d ≤ d * stepGateCount d := by
  unfold copyProtocolGateCount
  exact Nat.mul_le_mul_right _ hnd

theorem copyProtocolGateCount_budget (T k d : ℕ) :
    copyProtocolGateCount (copyPrecisionBudget T k) d
      ≤ (8 * T * T * 2 ^ k + 1) * stepGateCount d := by
  unfold copyProtocolGateCount copyPrecisionBudget
  have hmax : max 1 (8 * T * T * 2 ^ k) ≤ 8 * T * T * 2 ^ k + 1 := by
    apply max_le <;> omega
  exact Nat.mul_le_mul_right _ hmax

theorem paperMatrix_rank_le {m d : ℕ} (O : ColumnOracle m d) :
    (paperMatrix O).rank ≤ m := by
  have hmat : paperMatrix O = (gramMatrix O.col O.norm)ᵀ := by
    have h2 : paperMatrix O = (marginal O)ᵀ := by
      rw [marginal_eq_paperMatrix_transpose, Matrix.transpose_transpose]
    rw [h2, marginal_eq_gramMatrix]
  rw [hmat, Matrix.rank_transpose]
  have hgram : gramMatrix O.col O.norm
      = (gramColumn O.col O.norm)ᴴ * (gramColumn O.col O.norm) := rfl
  rw [hgram, Matrix.rank_conjTranspose_mul_self]
  have := Matrix.rank_le_card_width (gramColumn O.col O.norm)
  simpa using this

theorem paperMatrix_rank_le_min {m d : ℕ} (O : ColumnOracle m d) :
    (paperMatrix O).rank ≤ min m d := by
  have hmat : paperMatrix O = (gramMatrix O.col O.norm)ᵀ := by
    have h2 : paperMatrix O = (marginal O)ᵀ := by
      rw [marginal_eq_paperMatrix_transpose, Matrix.transpose_transpose]
    rw [h2, marginal_eq_gramMatrix]
  rw [hmat, Matrix.rank_transpose]
  have hgram : gramMatrix O.col O.norm
      = (gramColumn O.col O.norm)ᴴ * (gramColumn O.col O.norm) := rfl
  rw [hgram, Matrix.rank_conjTranspose_mul_self]
  refine le_min ?_ ?_
  · simpa using Matrix.rank_le_card_width (gramColumn O.col O.norm)
  · simpa using Matrix.rank_le_card_height (gramColumn O.col O.norm)

end Qatlib.Papers.QuantumPCA14.InputAccess
