/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.QueryBudgetSuccess
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

def Theorem1QueryBudgetCorrected : Prop :=
  (∀ (N : ℕ) (_hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α),
    (1 / 2 : ℝ) ≤ minimumInitialSuccess T (minimumQueryBudget N) ∧
    minimumInitialSuccess T (minimumQueryBudget N) ≤ 1 ∧
    (∀ current : Fin N, minimumBudgetEval T (minimumQueryBudget N) current (fun _ _ => 1) = 1) ∧
    (∀ (current : Fin N) (f g : Fin N → ℕ → ℝ),
      (∀ i r, r ≤ minimumQueryBudget N → f i r = g i r) →
      minimumBudgetEval T (minimumQueryBudget N) current f =
        minimumBudgetEval T (minimumQueryBudget N) current g) ∧
    (minimumQueryBudget N : ℝ) ≤ 59 * Real.sqrt N) ∧
  Asymptotics.IsBigO Filter.atTop (fun N : ℕ => (minimumQueryBudget N : ℝ))
    (fun N : ℕ => Real.sqrt (N : ℝ))

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
