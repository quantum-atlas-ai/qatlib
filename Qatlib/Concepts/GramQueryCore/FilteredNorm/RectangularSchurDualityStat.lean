/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def RectangularSchurDuality : Prop :=
  ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
    sourceRectValue A Z = sourceRectDual A Z ∧
    (sourceRectValue A Z < ⊤ → ∃ M : Matrix R S ℂ,
      (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ sourceRectValue A Z=ENNReal.ofReal ‖A ⊙ M‖) ∧
    (sourceRectValue A Z = ⊤ → ∀ t : ℝ, ∃ M : Matrix R S ℂ,
      (∀ j, ‖Z j ⊙ M‖ ≤ 1) ∧ t ≤ ‖A ⊙ M‖)
end Qatlib.Concepts.GramQueryCore.FilteredNorm
