/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkDiff01.MainResults.Defs

/-!
# The quantum column propagator at time zero

The matrix-exponential evolution `quantumPropagator` associated with the reduced glued-tree
Hamiltonian equals the identity at time zero. The result supplies the initial condition for the
column-space quantum evolution. The mathematical setting is described in
[ChildsFarhiGutmann2002].

## Main statements

* `quantumPropagator_zero`: the propagator at zero is the identity matrix.

## References

* [Childs et al., 2002][ChildsFarhiGutmann2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- The quantum column propagator at time zero is the identity matrix. -/
theorem quantumPropagator_zero (n : ℕ) (γ : ℝ) :
    quantumPropagator n γ 0 = 1 := by
  simp [quantumPropagator]

end Qatlib.Papers.QWalkDiff01.MainResults
