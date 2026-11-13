/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.GOpers

/-!
# Normalization of the finite abelian character pairing

The sum of coordinate character values does not have the normalization required of the character
pairing: at zero in two coordinates it equals two. The product pairing `charPair` has value one
at zero, providing the corrected normalization used in the Fourier development. The development
follows [BrassardHoyer1997].

## Main statements

* `printedPairing_zero_counter`: evaluates the sum pairing at zero in two binary coordinates.
* `correctedPairing_zero`: checks the product pairing at zero.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ExactSimon97.MainResults

/-- The sum of coordinate additive character values in the pairing formula under examination. -/
def printedPairing {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) : ℂ :=
  ∑ i, @ZMod.stdAddChar (m i) (hnz i) (g i * h i)

/-- For two binary coordinates, the sum pairing evaluated at zero and zero equals two. See
[BrassardHoyer1997]. -/
theorem printedPairing_zero_counter :
    printedPairing (m := fun _ : Fin 2 => 2) 0 0 = 2 := by
  simp [printedPairing]

/-- For two binary coordinates, the sum pairing at zero and zero is not one. See
[BrassardHoyer1997]. -/
theorem printedPairing_not_normalized :
    printedPairing (m := fun _ : Fin 2 => 2) 0 0 ≠ 1 := by
  rw [printedPairing_zero_counter]
  norm_num

/-- The product character pairing evaluated at zero and zero equals one. See
[BrassardHoyer1997]. -/
theorem correctedPairing_zero {n : ℕ} {m : Fin n → ℕ} [∀ i, NeZero (m i)] :
    charPair (m := m) 0 0 = 1 := by
  simp [charPair]

end Qatlib.Papers.ExactSimon97.MainResults
