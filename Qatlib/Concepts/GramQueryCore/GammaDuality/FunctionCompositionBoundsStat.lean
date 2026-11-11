/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Function composition bound specification

The proposition `FunctionCompositionBounds` states a guarded upper bound for compatible outer
and inner inputs and a product lower bound for independent copies of a Boolean-valued inner
function. It packages the adversary composition estimates associated with [LeeEtAl2011].

## Main statements

* `FunctionCompositionBounds`: The conjunction of a guarded adversary upper bound for compatible
  outer and inner inputs and a product lower bound for independent Boolean-valued inner
  functions.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.GammaDuality
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The conjunction of a guarded adversary upper bound for compatible outer and inner inputs and
a product lower bound for independent Boolean-valued inner functions. -/
def FunctionCompositionBounds : Prop :=
  (∀ (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
      [Fintype E] [DecidableEq E] (n m q a : ℕ)
      (inner : X → Fin n → Fin (q+1)) (g : X → Fin (a+1))
      (outer : Y → Fin m → Fin (a+1)) (f : Y → E),
      let D := {p : Y × (Fin m → X) // ∀ j, outer p.1 j=g (p.2 j)}
      let input := fun p : D => sourceIndependentInput inner m p.1.2
      let result := fun p : D => f p.1.1
      (sourceAdversary (sourceAlphabetDelta outer) f < ⊤ ∨
        sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner) ≠ 0) →
      sourceAdversary (sourceAlphabetDelta input) result ≤
        sourceAdversary (sourceAlphabetDelta outer) f *
          sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner)) ∧
  (∀ (X E : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
      (n m q : ℕ) (inner : X → Fin n → Fin (q+1)) (g : X → Bool)
      (f : (Fin m → Bool) → E),
      sourceAdversary (sourceAlphabetDelta (sourceIndependentInput inner m))
        (fun xs => f (fun j => g (xs j))) ≥
        sourceAdversary (sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j))) f *
          sourceAdversary (sourceAlphabetDelta inner) g)
end Qatlib.Concepts.GramQueryCore.GammaDuality
