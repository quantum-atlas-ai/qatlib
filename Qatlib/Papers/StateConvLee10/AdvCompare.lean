/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan

/-!
# Adversary and filtered-norm comparison

This module exposes the function-evaluation adversary quantity and its comparison with a
rectangular filtered norm. The comparison includes the factor `2 * (1 - 1 / |E|)` and a
representation using output-filtered query differences, following [LeeEtAl2011].

## Main statements

* `source_real_adversary`: the adversary quantity for the supplied input encoding.
* `source_adversary_comparison`: the function-evaluation filtered norm is sandwiched between
  adversary bounds.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.GramQueryCore.FilteredNorm

namespace Qatlib.Papers.StateConvLee10.AdvCompare

/-- The function-evaluation adversary quantity associated with the alphabet-difference filters
of `input` [LeeEtAl2011]. -/
def source_real_adversary {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) : ℝ≥0∞ :=
  sourceAdversary (sourceAlphabetDelta input) f

/-- The function-evaluation matrix has the stated unfiltered-norm bound, the adversary equals
the output-filtered rectangular norm, and the original filtered norm lies between the
adversary and its stated output-cardinality multiple [LeeEtAl2011]. -/
theorem source_adversary_comparison :
  ∀ (X E : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    (n q : ℕ) (input : X → Fin n → Fin (q+1)) (f : X → E),
    let A := gramFunctionEvaluationMatrix f
    let Z := sourceAlphabetDelta input
    sourceUnfiltered A ≤ ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ))) ∧
    sourceAdversary Z f = sourceRectValue A (fun j => Z j ⊙ A) ∧
    sourceAdversary Z f ≤ sourceRectValue A Z ∧
    sourceRectValue A Z ≤ ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ)))*sourceAdversary Z f := by
  exact Qatlib.Concepts.GramQueryCore.FilteredNorm.functionEvaluationNormSandwich

end Qatlib.Papers.StateConvLee10.AdvCompare
