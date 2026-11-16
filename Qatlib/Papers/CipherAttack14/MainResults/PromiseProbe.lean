/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CipherAttack14.MainResults.KeTwoClaw
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section


/-! # Uniqueness of a key pair does not make each list injective
This checks a limitation of the archived cut-function reduction. Its explicit
list-injectivity premises cannot be discharged from the key-pair promise alone.
-/
set_option autoImplicit false
namespace Qatlib.Papers.CipherAttack14.MainResults
open Qatlib.Papers.CipherAttack14.MainResults

/-- Three actual permutations with a unique successful double encryption. -/
def exampleFamily : PermFamily 3 3 := fun k =>
  if k = 0 then Equiv.refl _ else if k = 1 then Equiv.swap 1 2 else Equiv.swap 0 1

/-- The key-pair promise holds in the concrete example. -/
theorem uniquePair : keyPairs exampleFamily 0 2 = {(2, 1)} := by decide

/-- The forward list still repeats a value away from the solution. -/
theorem repeatedList : ¬ Function.Injective (forwardList exampleFamily 0) := by
  intro h
  have heq : forwardList exampleFamily 0 0 = forwardList exampleFamily 0 1 := by decide
  have h01 := h heq
  exact (by decide : (0 : Fin 3) ≠ 1) h01

end Qatlib.Papers.CipherAttack14.MainResults
