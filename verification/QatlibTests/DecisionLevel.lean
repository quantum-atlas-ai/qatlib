/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred

@[expose] public section

/-! Concrete positive and negative instances of the horizontal-predicate helpers.
These check local identification and the final promised decision, without claiming
an expected-query bound for a global adaptive process. -/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.DecisionLevel

open Qatlib.Papers.DecisionTrees97.ClassicalWord.LevelPred

/-- A matching first bit and a mismatching second bit produce an informative answer. -/
theorem forcing :
    lvlAuxF false (fun _ : Fin 2 => false) (fun i => decide (i = 1)) = true := by
  decide

/-- A first-bit mismatch returns the original flag rather than the informative answer. -/
theorem mismatch :
    lvlAuxF false (fun _ : Fin 2 => false) (fun _ => true) = false := by
  decide

/-- Under uniform two-bit sampling, informative answers have positive mass. -/
theorem uniformMass :
    (informativeSet 0 2 (fun _ => false)).card = 2 := by
  decide

/-- A known prefix restricts query words while leaving the final bit free. -/
theorem prefixCount :
    (prefixFixed 1 1 (fun _ => false)).card = 2 := by
  decide

/-- After one fixed prefix bit, the opposite parity attains the quarter-mass boundary. -/
theorem quarterMass :
    (informativeSet 1 2 (fun _ => false)).card = 1 := by
  decide

/-- The two endpoint evaluations decide a concrete nonempty promised predicate. -/
theorem endpoint :
    ∃ p : (Fin 1 → Bool) × Bool, (p.1 0 == false && p.2) = true := by
  exact ⟨(fun _ => false, true), rfl⟩

/-- The support promise is necessary: a different prefix can conceal a true endpoint. -/
theorem needPromise :
    (∃ p : (Fin 1 → Bool) × Bool, p.1 0 = true) ∧
      ¬ ((fun _ : Fin 1 => false) 0 = true) := by
  exact ⟨⟨(fun _ => true, false), rfl⟩, Bool.false_ne_true⟩

end QatlibTests.DecisionLevel
