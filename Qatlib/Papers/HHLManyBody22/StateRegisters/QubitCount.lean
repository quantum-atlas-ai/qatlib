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

/-!
# State-register qubit counts

`stateRegisterQubits` assigns the ceiling binary logarithm to an excitation-space dimension,
while `qpeStateQubits` assigns one state qubit per spin orbital. These counts express the
state-register comparison in [BaskaranEtAl2023].

The module characterizes register-size bounds by powers of two and derives weak and strict
comparisons from corresponding dimension bounds.

## Main statements

* `stateRegisterQubits_le_iff`: characterizes when a dimension fits in a given binary register.
* `stateRegisterQubits_two_pow`: computes the register size for a power-of-two dimension.
* `hhlQubits_lt_qpeQubits`: derives a strict state-qubit saving from a dimension bound.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HHLManyBody22.StateRegisters

/-- The state-register qubit count `Nat.clog 2 dim` for a space of dimension `dim`. -/
def stateRegisterQubits (dim : ℕ) : ℕ := Nat.clog 2 dim

/-- The QPE state-register qubit count with one qubit for each spin orbital. -/
def qpeStateQubits (spinOrbitals : ℕ) : ℕ := spinOrbitals

/-- The state-register count is the ceiling binary logarithm `Nat.clog 2 dim`. -/
theorem stateRegisterQubits_def (dim : ℕ) :
    stateRegisterQubits dim = Nat.clog 2 dim := rfl

/-- The QPE state-register count equals the number of spin orbitals. -/
theorem qpeStateQubits_def (spinOrbitals : ℕ) :
    qpeStateQubits spinOrbitals = spinOrbitals := rfl

/-- The state-register count is at most `k` exactly when the dimension is at most `2 ^ k`. -/
theorem stateRegisterQubits_le_iff {dim k : ℕ} :
    stateRegisterQubits dim ≤ k ↔ dim ≤ 2 ^ k := by
  unfold stateRegisterQubits
  exact Nat.clog_le_iff_le_pow (by norm_num)

/-- A space of dimension `2 ^ k` requires exactly `k` state-register qubits. -/
theorem stateRegisterQubits_two_pow (k : ℕ) :
    stateRegisterQubits (2 ^ k) = k := by
  unfold stateRegisterQubits
  exact Nat.clog_pow 2 k (by norm_num)

/-- If the excitation dimension is at most `2 ^ nso`, its state-register count is at most the
QPE state-register count for `nso` spin orbitals. -/
theorem hhlQubits_le_qpeQubits {dim nso : ℕ} (h : dim ≤ 2 ^ nso) :
    stateRegisterQubits dim ≤ qpeStateQubits nso := by
  rw [qpeStateQubits_def]
  exact stateRegisterQubits_le_iff.mpr h

/-- For a positive spin-orbital count, a dimension at most `2 ^ (nso - 1)` gives a strictly
smaller state-register count than the QPE encoding. -/
theorem hhlQubits_lt_qpeQubits {dim nso : ℕ} (hn : 0 < nso)
    (h : dim ≤ 2 ^ (nso - 1)) :
    stateRegisterQubits dim < qpeStateQubits nso := by
  have hle : stateRegisterQubits dim ≤ nso - 1 :=
    stateRegisterQubits_le_iff.mpr h
  rw [qpeStateQubits_def]
  exact Nat.lt_of_le_of_lt hle (Nat.sub_lt hn (by norm_num : 0 < 1))

end Qatlib.Papers.HHLManyBody22.StateRegisters
