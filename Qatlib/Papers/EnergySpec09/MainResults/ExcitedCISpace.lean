/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.EnergySpec09.MainResults.FewCSFTruncation

@[expose] public section

/-!
# Computational-basis register for the excited-state CI space

Section V uses 18 configuration state functions. A five-qubit register
has room for these labels, and any lossless computational-basis encoding
requires at least five qubits.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.EnergySpec09.MainResults

/-- The 18 configuration state functions in the excited-state simulation
require a five-qubit register by the ceiling-logarithm count. -/
theorem excited_ci_register_qubits : Nat.clog 2 18 = 5 := by decide

/-- Use the first 18 labels of the existing five-bit register enumeration. -/
def excitedCILabelEncoding : Fin 18 ↪ Reg 5 :=
  (Fin.castLEEmb (by decide : 18 ≤ 2 ^ 5)).trans (bitVecEquiv 5).symm.toEmbedding

/-- Any injective encoding of the 18 configuration labels into a qubit
basis register requires at least five qubits. -/
theorem excited_ci_register_minimal (q : ℕ) (encode : Fin 18 ↪ Reg q) :
    5 ≤ q := by
  have hcard := Fintype.card_le_of_injective encode encode.injective
  rw [Fintype.card_fin, card_reg] at hcard
  have h := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hcard
  rwa [excited_ci_register_qubits] at h

end Qatlib.Papers.EnergySpec09.MainResults
