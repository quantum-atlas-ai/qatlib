/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodySim96.MainResults.Basic

/-!
# A nonunitary first-order Taylor step

`oneBodyProjector` gives a Hermitian two-dimensional example for which the positive-sign
first-order Taylor matrix is not unitary at any nonzero time step. This records the distinction
between the Taylor approximation and exact unitary evolution in the finite many-body simulation
model.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `oneBodyProjector_isHermitian`: The one-body diagonal projector is Hermitian.
* `taylorStep_projector_not_unitary`: For every nonzero real step size, the first-order Taylor
  matrix of the one-body projector is not unitary.

## References

* [Wiesner, 1996][Wiesner1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ManyBodySim96.MainResults

/-- The two-dimensional diagonal projector with entries `1` and `0`. -/
def oneBodyProjector : Operator 2 := Matrix.diagonal ![1, 0]

/-- The one-body diagonal projector is Hermitian. -/
theorem oneBodyProjector_isHermitian : oneBodyProjector.IsHermitian := by
  show oneBodyProjectorᴴ = oneBodyProjector
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [oneBodyProjector, Matrix.conjTranspose_apply]

/-- For every nonzero real step size, the first-order Taylor matrix of the one-body projector is
not unitary. [Wiesner1996] -/
theorem taylorStep_projector_not_unitary (dt : ℝ) (hdt : dt ≠ 0) :
    taylorStep oneBodyProjector dt ∉ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro hu
  have h := congrArg (fun A : Operator 2 => (A 0 0).re)
    (Matrix.mem_unitaryGroup_iff'.mp hu)
  simp [taylorStep, oneBodyProjector, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im] at h
  nlinarith [sq_pos_of_ne_zero hdt]

end Qatlib.Papers.ManyBodySim96.MainResults
