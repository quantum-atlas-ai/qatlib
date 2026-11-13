/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.Dirichlet
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost

/-!
# Dirichlet-character phase changes

The theorem `lemma3_dirichletPhaseChange` collects the unit-support and norm properties of
`DirichletChar`. Multiplication by the character preserves squared norm for states supported on
units, and the stated specification cost remains polylogarithmic after adding constant overhead.
See [VanDamSeroussi2002].

## Main statements

* `lemma3_dirichletPhaseChange`: A Dirichlet character has unit norm on units and vanishes on
  nonunits, so multiplication by it preserves the total squared norm of unit-supported states. A
  polylogarithmic specification cost remains polylogarithmic after adding two.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- A Dirichlet character has unit norm on units and vanishes on nonunits, so multiplication by
it preserves the total squared norm of unit-supported states. A polylogarithmic
specification cost remains polylogarithmic after adding two [VanDamSeroussi2002]. -/
theorem lemma3_dirichletPhaseChange (n : ℕ) [NeZero n] (χ : DirichletChar n)
    (spec : ℕ → ℕ) (hspec : PolyLog spec) :
    (∀ x : ZMod n, IsUnit x → ‖χ.toFun x‖ = 1) ∧
    (∀ x : ZMod n, ¬ IsUnit x → χ.toFun x = 0) ∧
    (∀ ψ : ZMod n → ℂ, (∀ x : ZMod n, ¬ IsUnit x → ψ x = 0) →
      (∑ x : ZMod n, ‖χ.toFun x * ψ x‖ ^ 2) = ∑ x : ZMod n, ‖ψ x‖ ^ 2) ∧
    PolyLog (fun k => spec k + 2) := by
  refine ⟨χ.norm_eq_one, χ.map_zero_of_not_unit, ?_,
    polyLog_add hspec (polyLog_const 2 (by norm_num))⟩
  intro ψ hψ
  exact dirichlet_phaseChange_isometry χ ψ hψ

end Qatlib.Papers.GaussSumEst02.MainResults.Claims
