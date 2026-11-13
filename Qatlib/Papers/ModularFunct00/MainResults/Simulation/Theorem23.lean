/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Approximation.Theorem21
import Qatlib.Papers.ModularFunct00.MainResults.Representation.EquivUpToPhase

/-!
# Unitary products and a simulation error bound

This module proves that a finite product of unitary matrices remains unitary and records a
numerical consequence of an error bound of one tenth. These are elementary supporting steps for
the simulation discussion surrounding Theorem 2.3 of [FreedmanLarsenWang2000].

## Main statements

* `list_prod_mem_unitaryGroup`: A list product of unitary matrices is unitary.
* `theorem2_3_success_probability`: The supplied error budget implies `1 - err ≥ 3 / 4`.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Simulation

open Matrix
open scoped Matrix.Norms.L2Operator

/-- If every matrix in a list belongs to the unitary group, then their product belongs to the
unitary group; see [FreedmanLarsenWang2000]. -/
lemma list_prod_mem_unitaryGroup {d : ℕ} (l : List (CM d))
    (h : ∀ x ∈ l, x ∈ unitaryGroup (Fin d) ℂ) :
    l.prod ∈ unitaryGroup (Fin d) ℂ := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact Representation.unitary_mul (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- If `err ≤ 1 / 10`, then `1 - err` is at least three quarters; see [FreedmanLarsenWang2000]. -/
theorem theorem2_3_success_probability
    (err : ℝ) (h : err ≤ 1 / 10) :
    3 / 4 ≤ 1 - err :=
  Approximation.theorem2_1_success_from_error h

end Qatlib.Papers.ModularFunct00.MainResults.Simulation
