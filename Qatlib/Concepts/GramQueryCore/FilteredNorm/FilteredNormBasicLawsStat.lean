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

def FilteredNormBasicLaws : Prop :=
  ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (n : ℕ) (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
    (A ≠ 0 → sourceRectValue A (fun _ : Fin 1 => A)=1) ∧
    (sourceRectValue A Z=0 ↔ A=0) ∧
    (sourceRectValue A Z=⊤ ↔ ¬sourceSupports A Z) ∧
    (∀ c : ℂ, sourceRectValue (c • A) Z=ENNReal.ofReal ‖c‖*sourceRectValue A Z) ∧
    (∀ c : ℂ, c ≠ 0 → sourceRectValue A (fun j => c • Z j)=
      (ENNReal.ofReal ‖c‖)⁻¹*sourceRectValue A Z) ∧
    sourceRectValue (A+B) Z ≤ sourceRectValue A Z+sourceRectValue B Z ∧
    sourceRectValue (A ⊙ B) Z ≤ sourceRectValue A Z*sourceUnfiltered B ∧
    sourceRectValue (A ⊙ B) (fun j => Z j ⊙ B) ≤ sourceRectValue A Z ∧
    ((sourceRectValue A (fun j => Z j ⊙ B) < ⊤ ∨ B ≠ 0) →
      sourceRectValue A Z ≤ sourceRectValue A (fun j => Z j ⊙ B)*sourceUnfiltered B)
end Qatlib.Concepts.GramQueryCore.FilteredNorm
