/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.Dirichlet
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

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
