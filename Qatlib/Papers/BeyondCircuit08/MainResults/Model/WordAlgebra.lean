/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Model

open scoped Matrix BigOperators

theorem evalWord_append {M : Type} [Monoid M] [Inv M] {n : ℕ}
    (gen : Fin (n - 1) → M) (w₁ w₂ : BraidWord n) :
    evalWord gen (List.append w₁ w₂) = evalWord gen w₁ * evalWord gen w₂ := by
  simp [evalWord, List.map_append, List.prod_append]

theorem evalWord_nil {M : Type} [Monoid M] [Inv M] {n : ℕ}
    (gen : Fin (n - 1) → M) : evalWord gen [] = 1 := rfl

theorem crossingCount_append {n : ℕ} (w₁ w₂ : BraidWord n) :
    crossingCount (List.append w₁ w₂) = crossingCount w₁ + crossingCount w₂ := by
  simp [crossingCount]

theorem crossingCount_singleton {n : ℕ} (g : Fin (n - 1) × Bool) :
    crossingCount [g] = 1 := rfl

end Qatlib.Papers.BeyondCircuit08.MainResults.Model
