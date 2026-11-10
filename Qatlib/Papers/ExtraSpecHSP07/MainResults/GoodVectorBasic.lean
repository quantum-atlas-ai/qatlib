/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

open scoped BigOperators

theorem isWitness_zero (p : ℕ) : IsWitness p 0 (fun _ => (1 : (ZMod p)ˣ)) := by
  unfold IsWitness
  constructor <;> simp

theorem isGoodVector_zero (p : ℕ) : IsGoodVector p 0 :=
  ⟨fun _ => 1, isWitness_zero p⟩

theorem exists_isGoodVector (p : ℕ) : ∃ u : Fin 4 → ZMod p, IsGoodVector p u :=
  ⟨0, isGoodVector_zero p⟩

end Qatlib.Papers.ExtraSpecHSP07.MainResults
