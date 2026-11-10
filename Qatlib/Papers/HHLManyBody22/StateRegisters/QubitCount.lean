/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HHLManyBody22.StateRegisters

def stateRegisterQubits (dim : ℕ) : ℕ := Nat.clog 2 dim

def qpeStateQubits (spinOrbitals : ℕ) : ℕ := spinOrbitals

theorem stateRegisterQubits_def (dim : ℕ) :
    stateRegisterQubits dim = Nat.clog 2 dim := rfl

theorem qpeStateQubits_def (spinOrbitals : ℕ) :
    qpeStateQubits spinOrbitals = spinOrbitals := rfl

theorem stateRegisterQubits_le_iff {dim k : ℕ} :
    stateRegisterQubits dim ≤ k ↔ dim ≤ 2 ^ k := by
  unfold stateRegisterQubits
  exact Nat.clog_le_iff_le_pow (by norm_num)

theorem stateRegisterQubits_two_pow (k : ℕ) :
    stateRegisterQubits (2 ^ k) = k := by
  unfold stateRegisterQubits
  exact Nat.clog_pow 2 k (by norm_num)

theorem hhlQubits_le_qpeQubits {dim nso : ℕ} (h : dim ≤ 2 ^ nso) :
    stateRegisterQubits dim ≤ qpeStateQubits nso := by
  rw [qpeStateQubits_def]
  exact stateRegisterQubits_le_iff.mpr h

theorem hhlQubits_lt_qpeQubits {dim nso : ℕ} (hn : 0 < nso)
    (h : dim ≤ 2 ^ (nso - 1)) :
    stateRegisterQubits dim < qpeStateQubits nso := by
  have hle : stateRegisterQubits dim ≤ nso - 1 :=
    stateRegisterQubits_le_iff.mpr h
  rw [qpeStateQubits_def]
  exact Nat.lt_of_le_of_lt hle (Nat.sub_lt hn (by norm_num : 0 < 1))

end Qatlib.Papers.HHLManyBody22.StateRegisters
