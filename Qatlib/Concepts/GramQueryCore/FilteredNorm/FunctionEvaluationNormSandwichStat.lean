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
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def FunctionEvaluationNormSandwich : Prop :=
  ∀ (X E : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    (n q : ℕ) (input : X → Fin n → Fin (q+1)) (f : X → E),
    let A := gramFunctionEvaluationMatrix f
    let Z := sourceAlphabetDelta input
    sourceUnfiltered A ≤ ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ))) ∧
    sourceAdversary Z f = sourceRectValue A (fun j => Z j ⊙ A) ∧
    sourceAdversary Z f ≤ sourceRectValue A Z ∧
    sourceRectValue A Z ≤ ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ)))*sourceAdversary Z f
end Qatlib.Concepts.GramQueryCore.FilteredNorm
