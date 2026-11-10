/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator
open Matrix

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.EvalRelaxed

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
