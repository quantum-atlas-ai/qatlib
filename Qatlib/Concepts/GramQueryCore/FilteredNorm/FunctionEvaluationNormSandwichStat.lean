/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Function evaluation sandwich specification

The proposition `FunctionEvaluationNormSandwich` states the unfiltered evaluation-matrix bound,
the masked-filter adversary identity, and a two-sided comparison with the unmasked rectangular
value. Its comparison factor depends on the cardinality of the finite output type, as in the
function-evaluation analysis of [LeeEtAl2011].

## Main statements

* `FunctionEvaluationNormSandwich`: The bundled unfiltered bound, masked adversary identity, and
  two-sided comparison between the adversary value and the rectangular query-filtered value for
  finite-output functions.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The bundled unfiltered bound, masked adversary identity, and two-sided comparison between
the adversary value and the rectangular query-filtered value for finite-output functions. -/
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
