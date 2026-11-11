/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Guarded positive-interval repair

`positiveIntervalRepairWeight` and `positiveIntervalRepairGuard` define an affine rescaling
procedure for approximations to matrices in a positive interval. `positiveIntervalRepair` shifts
and rescales matrices passing the guard and returns zero otherwise.

The construction is expressed using positive semidefinite order, as developed in [Bhatia1997].
Interval membership and approximation bounds are proved in the companion module.

## Main statements

* `positiveIntervalRepairWeight`: The scalar rescaling factor `q / (q + 2 * r)`.
* `positiveIntervalRepairGuard`: The relaxed matrix-order bounds needed by the repair.
* `positiveIntervalRepair`: The guarded shifted-and-rescaled matrix.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Classical Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The scalar repair weight `q / (q + 2 * r)`. -/
noncomputable def positiveIntervalRepairWeight (q r : ℝ) : ℝ := q / (q + 2*r)

/-- The condition that `M + r • 1` and `(q + r) • 1 - M` are positive semidefinite. -/
def positiveIntervalRepairGuard (M : Matrix N N ℂ) (q r : ℝ) : Prop :=
  (M + r • (1 : Matrix N N ℂ)).PosSemidef ∧
  ((q+r) • (1 : Matrix N N ℂ) - M).PosSemidef

/-- The matrix `positiveIntervalRepairWeight q r • (M + r • 1)` when the repair guard holds, and
zero otherwise. -/
noncomputable def positiveIntervalRepair (M : Matrix N N ℂ) (q r : ℝ) : Matrix N N ℂ :=
  if positiveIntervalRepairGuard M q r then
    positiveIntervalRepairWeight q r • (M + r • (1 : Matrix N N ℂ)) else 0

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
