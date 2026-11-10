/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Approximation.Theorem21
import Qatlib.Papers.ModularFunct00.MainResults.Representation.EquivUpToPhase
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Simulation

open Matrix
open scoped Matrix.Norms.L2Operator

lemma list_prod_mem_unitaryGroup {d : ℕ} (l : List (CM d))
    (h : ∀ x ∈ l, x ∈ unitaryGroup (Fin d) ℂ) :
    l.prod ∈ unitaryGroup (Fin d) ℂ := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact Representation.unitary_mul (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem theorem2_3_success_probability
    (err : ℝ) (h : err ≤ 1 / 10) :
    3 / 4 ≤ 1 - err :=
  Approximation.theorem2_1_success_from_error h

end Qatlib.Papers.ModularFunct00.MainResults.Simulation
