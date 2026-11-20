/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Papers.ClassShadows20.SampleBudget.PilotExecution

/-!
# Regression consumers for executed pilot resources

Exercise signed samples, empty input, a uniform family, and the impossibility of
zero cost for a nonempty table. The examples verify the exact outputs and the arithmetic cost guarantees.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.PilotExecution

open Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments
open Qatlib.Papers.ClassShadows20.SampleBudget
open Qatlib.Concepts.MonteCarloMean.PilotVariance

private def pilotRecordCount (samples : List ℚ) : ℕ :=
  (run samples).records

example : pilotRecordCount [1, -1] = 2 := rfl

example : (run [1, -1]).mean = 0 ∧ (run [1, -1]).secondMoment = 1 := by
  have h := run_values [1, -1]
  norm_num at h ⊢
  exact ⟨h.1, h.2.1⟩

example : (run []).mean = 0 ∧ (run []).secondMoment = 0 := by
  have h := run_values []
  simpa using And.intro h.1 h.2.1

example (as : List ℚ) (h : as ≠ []) : (run as).bitOps ≠ 0 := by
  have hlen : 0 < as.length := List.length_pos_iff.mpr h
  have hcost := run_cost_lower as
  omega

example {I : Type} (N : ℕ) (f : I → ℚ) (omega : Fin N → I) :
    let r := run (List.ofFn fun i => f (omega i))
    (r.mean, r.secondMoment, r.records) = pilotMoments N f omega :=
  pilot_moments_execution N f omega

example : ∃ c e : ℕ, ∀ n : ℕ, (run [1, -1]).bitOps ≤ c * (n + 1) ^ e := by
  exact run_family_polynomial (fun _ => [1, -1]) (encodedSize [1, -1]) 0 (by simp)

#print axioms pilot_moments_execution
#print axioms run_cost_bound

end QatlibTests.PilotExecution
