/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value

/-!
# Evaluation relaxation comparison specification

`AdversaryGamma2Sandwich` states two comparisons between filtered γ₂ values with and without the
function evaluation mask. The same proposition includes an operator norm bound for matrices with
zero equal-output blocks and contractive query-filtered matrices.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `AdversaryGamma2Sandwich`: The value sandwich and the feasible matrix norm bound.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator
open Matrix

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.EvalRelaxed

/-- The statement comparing evaluation-masked and unmasked filtered γ₂ values by the factor `2 *
(1 - 1 / Fintype.card E)` and bounding the norm of every matrix with zero equal-output
blocks and contractive query filters by the masked value. -/
def AdversaryGamma2Sandwich : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X]
    (E : Type) [Fintype E] [DecidableEq E] (n : ℕ)
    (input : X → Fin n → Bool) (f : X → E),
    filteredGamma2 (gramFunctionEvaluationMatrix f)
        (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) ≤
      filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input)
    ∧ filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ≤
      ENNReal.ofReal (2 * (1 - 1 / (Fintype.card E : ℝ))) *
        filteredGamma2 (gramFunctionEvaluationMatrix f)
          (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y)
    ∧ ∀ Γ : Matrix X X ℂ,
      (∀ x y, f x = f y → Γ x y = 0) →
      (∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) →
      ENNReal.ofReal ‖Γ‖ ≤
        filteredGamma2 (gramFunctionEvaluationMatrix f)
          (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y)

end Qatlib.Concepts.ConversionCore.EvalRelaxed
