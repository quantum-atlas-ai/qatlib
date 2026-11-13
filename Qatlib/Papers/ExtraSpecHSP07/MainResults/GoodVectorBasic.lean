/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.Defs

/-!
# Zero witnesses for good vectors

The zero vector satisfies the witness equations with every witness coordinate equal to one.
Consequently, a good four-coordinate vector over `ZMod p` exists for every natural-number
modulus. These statements formalize components of [IvanyosSanselmeSantha2007].

## Main statements

* `isWitness_zero`: verifies the all-one witness for the zero vector.
* `exists_isGoodVector`: provides a good vector for every modulus.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

open scoped BigOperators

/-- The all-one vector of units is a witness for the zero vector over `ZMod p`. -/
theorem isWitness_zero (p : ℕ) : IsWitness p 0 (fun _ => (1 : (ZMod p)ˣ)) := by
  unfold IsWitness
  constructor <;> simp

/-- The zero vector is good over `ZMod p`. -/
theorem isGoodVector_zero (p : ℕ) : IsGoodVector p 0 :=
  ⟨fun _ => 1, isWitness_zero p⟩

/-- For every natural-number modulus `p`, there exists a good four-coordinate vector over `ZMod
p`. -/
theorem exists_isGoodVector (p : ℕ) : ∃ u : Fin 4 → ZMod p, IsGoodVector p u :=
  ⟨0, isGoodVector_zero p⟩

end Qatlib.Papers.ExtraSpecHSP07.MainResults
