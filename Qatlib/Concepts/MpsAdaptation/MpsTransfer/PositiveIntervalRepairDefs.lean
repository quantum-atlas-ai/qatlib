/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option autoImplicit false
namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Classical Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable def positiveIntervalRepairWeight (q r : ℝ) : ℝ := q / (q + 2*r)

def positiveIntervalRepairGuard (M : Matrix N N ℂ) (q r : ℝ) : Prop :=
  (M + r • (1 : Matrix N N ℂ)).PosSemidef ∧
  ((q+r) • (1 : Matrix N N ℂ) - M).PosSemidef

noncomputable def positiveIntervalRepair (M : Matrix N N ℂ) (q r : ℝ) : Matrix N N ℂ :=
  if positiveIntervalRepairGuard M q r then
    positiveIntervalRepairWeight q r • (M + r • (1 : Matrix N N ℂ)) else 0

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
