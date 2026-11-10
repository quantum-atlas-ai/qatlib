/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.GOpers
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ExactSimon97.MainResults

def printedPairing {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) : ℂ :=
  ∑ i, @ZMod.stdAddChar (m i) (hnz i) (g i * h i)

theorem printedPairing_zero_counter :
    printedPairing (m := fun _ : Fin 2 => 2) 0 0 = 2 := by
  simp [printedPairing]

theorem printedPairing_not_normalized :
    printedPairing (m := fun _ : Fin 2 => 2) 0 0 ≠ 1 := by
  rw [printedPairing_zero_counter]
  norm_num

theorem correctedPairing_zero {n : ℕ} {m : Fin n → ℕ} [∀ i, NeZero (m i)] :
    charPair (m := m) 0 0 = 1 := by
  simp [charPair]

end Qatlib.Papers.ExactSimon97.MainResults
