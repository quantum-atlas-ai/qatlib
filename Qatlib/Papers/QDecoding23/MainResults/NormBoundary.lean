/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QDecoding23.MainResults.Measurement

@[expose] public section


/-!
# The normalization boundary of the legacy two-state USD contract

The paper's pure states are unit vectors. The legacy QState carrier is an
unrestricted amplitude function, so zero states invalidate the purported
probability-one guarantee when no unit-norm hypotheses are supplied.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QDecoding23.MainResults

open Qatlib.Papers.QDecoding23.MainResults
open Qatlib.Foundations.PureStateMath

/-- Every POVM outcome has zero Born probability on the zero amplitude vector. -/
theorem zero_born {X I : Type} [Fintype X] [Fintype I] [DecidableEq I]
    (Λ : POVM X I) (a : X) : probPOVM Λ a (0 : QState I) = 0 := by
  simp [probPOVM, probOf, Qatlib.Foundations.PureStateMath.Inner]

/-- Without unit-norm assumptions the legacy two-state USD conclusion fails
on the pair of zero states, whose overlap norm is zero. -/
theorem usd_nonunit :
    ∃ (ψ0 ψ1 : QState (Fin 2)) (u : ℝ),
      ‖Qatlib.Foundations.PureStateMath.Inner ψ0 ψ1‖ = u ∧
      ¬ ∃ Λ : POVM (Fin 3) (Fin 2),
        probPOVM Λ (0 : Fin 3) ψ0 = 1 - u ∧
        probPOVM Λ (1 : Fin 3) ψ1 = 1 - u ∧
        probPOVM Λ (2 : Fin 3) ψ0 = u ∧ probPOVM Λ (2 : Fin 3) ψ1 = u := by
  refine ⟨0, 0, 0, ?_, ?_⟩
  · simp [Qatlib.Foundations.PureStateMath.Inner]
  · rintro ⟨Λ, h, _⟩
    simp only [zero_born, sub_zero, zero_ne_one] at h

end Qatlib.Papers.QDecoding23.MainResults
