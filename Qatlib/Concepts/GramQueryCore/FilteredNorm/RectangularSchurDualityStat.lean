/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Rectangular Schur duality specification

The proposition `RectangularSchurDuality` states equality between the rectangular filtered value
and its Schur multiplier dual. It includes a maximizing feasible multiplier when the value is
finite and arbitrarily large feasible objectives when it is infinite, in the setting of
[LeeEtAl2011].

## Main statements

* `RectangularSchurDuality`: Rectangular Schur duality, including attainment of finite values
  and unbounded feasible objectives when the value is infinite.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- Rectangular Schur duality, including attainment of finite values and unbounded feasible
objectives when the value is infinite. -/
def RectangularSchurDuality : Prop :=
  ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
    sourceRectValue A Z = sourceRectDual A Z ∧
    (sourceRectValue A Z < ⊤ → ∃ M : Matrix R S ℂ,
      (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ sourceRectValue A Z=ENNReal.ofReal ‖A ⊙ M‖) ∧
    (sourceRectValue A Z = ⊤ → ∀ t : ℝ, ∃ M : Matrix R S ℂ,
      (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ t ≤ ‖A ⊙ M‖)
end Qatlib.Concepts.GramQueryCore.FilteredNorm
