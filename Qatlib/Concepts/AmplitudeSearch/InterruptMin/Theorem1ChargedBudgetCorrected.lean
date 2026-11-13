/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedBudgetSuccess

/-!
# Corrected charged-budget minimum-finding specification

This module defines `Theorem1ChargedBudgetCorrected`, a proposition packaging a corrected
minimum-finding guarantee with initialization charges included. It requires success probability
between one half and one, normalization of the budget evaluator, dependence only on continuation
values within the budget, and explicit and asymptotic square-root bounds for `chargedBudget`.
The motivating minimum-finding setting is [DurrHoyer1996].

## Main statements

* `Theorem1ChargedBudgetCorrected`: the combined specification for `chargedInitialSuccess` and
  `minimumBudgetEvalWithInit`.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

/-- The corrected minimum-finding specification with initialization charges, requiring success
probability between one half and one, evaluator normalization, dependence only on
continuation values within the budget, and explicit and asymptotic square-root budget
bounds. This proposition expresses a charged-budget formulation of the minimum-finding
setting of [DurrHoyer1996]. -/
def Theorem1ChargedBudgetCorrected : Prop :=
  (∀ (N : ℕ) (_hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α),
    (1 / 2 : ℝ) ≤ chargedInitialSuccess T (chargedBudget N) ∧
    chargedInitialSuccess T (chargedBudget N) ≤ 1 ∧
    (∀ current : Fin N,
      minimumBudgetEvalWithInit T (initCharge N) (chargedBudget N) current (fun _ _ => 1) = 1) ∧
    (∀ (current : Fin N) (f g : Fin N → ℕ → ℝ),
      (∀ i r, r ≤ chargedBudget N → f i r = g i r) →
      minimumBudgetEvalWithInit T (initCharge N) (chargedBudget N) current f =
        minimumBudgetEvalWithInit T (initCharge N) (chargedBudget N) current g) ∧
    (chargedBudget N : ℝ) ≤
      (4 * ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) + 1) * Real.sqrt N) ∧
  Asymptotics.IsBigO Filter.atTop (fun N : ℕ => (chargedBudget N : ℝ))
    (fun N : ℕ => Real.sqrt (N : ℝ))

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
