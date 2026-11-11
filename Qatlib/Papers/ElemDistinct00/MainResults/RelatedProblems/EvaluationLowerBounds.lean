/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A finite collision-count bound

The quantity `collisionCount f` counts pairs `i < j` with `f i = f j`. The theorem
`collisionCount_le_sq` bounds this count by the cardinality `N * N` of all ordered pairs of
indices.

This elementary counting estimate belongs to the collision-problem framework used for the
evaluation-complexity discussion of [BuhrmanEtAl2005].

## Main statements

* `collisionCount_le_sq`: every function `Fin N → Fin N` has at most `N * N` counted collisions.

## References

* [Buhrman et al., 2005][BuhrmanEtAl2005], *Quantum Algorithms for Element Distinctness*,
  arXiv:quant-ph/0007016 (2000 preprint).
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

/-- The number of equal-image pairs `i < j` for a function on `Fin N` is at most `N * N`. This
elementary counting estimate belongs to the collision-problem framework of
[BuhrmanEtAl2005]. -/
theorem collisionCount_le_sq (N : ℕ) (f : Fin N → Fin N) :
    collisionCount f ≤ N * N := by
  unfold collisionCount
  calc (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ f p.1 = f p.2).card
      ≤ (Finset.univ : Finset (Fin N × Fin N)).card := Finset.card_filter_le _ _
    _ = N * N := by simp [Fintype.card_prod]

end Qatlib.Papers.ElemDistinct00.MainResults.RelatedProblems
