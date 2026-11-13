/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary collision facts

Element distinctness means that no two different inputs have the same image. The theorem
`elementDistinct_iff_not_hasCollision` exposes this definition, and `not_hasCollision_fin_one`
records the singleton case.

Despite the file name, these are a definitional equivalence and a singleton
collision fact; no element-distinctness query bound is proved in this module.

These basic collision facts support the element distinctness framework of [BuhrmanEtAl2005].

## Main statements

* `elementDistinct_iff_not_hasCollision`: element distinctness is equivalent to the absence of
  collisions.
* `not_hasCollision_fin_one`: a function on `Fin 1` has no collision.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.ElementDistinct

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- Element distinctness is equivalent to the absence of two distinct inputs with the same
image. This unfolds the predicate used in the element distinctness setting of
[BuhrmanEtAl2005]. -/
theorem elementDistinct_iff_not_hasCollision {X Z : Type*} (f : X → Z) :
    ElementDistinct f ↔ ¬ HasCollision f :=
  Iff.rfl

/-- A function from the singleton type `Fin 1` to the integers has no collision. This records a
degenerate case of the element distinctness setting in [BuhrmanEtAl2005]. -/
theorem not_hasCollision_fin_one (f : Fin 1 → ℤ) : ¬ HasCollision f := by
  rintro ⟨x, y, hxy, -⟩
  exact hxy (Subsingleton.elim x y)

end Qatlib.Papers.ElemDistinct00.MainResults.ElementDistinct
