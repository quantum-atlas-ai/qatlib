/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodySim96.MainResults.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ManyBodySim96.MainResults

def oneBodyProjector : Operator 2 := Matrix.diagonal ![1, 0]

theorem oneBodyProjector_isHermitian : oneBodyProjector.IsHermitian := by
  show oneBodyProjectorᴴ = oneBodyProjector
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [oneBodyProjector, Matrix.conjTranspose_apply]

theorem taylorStep_projector_not_unitary (dt : ℝ) (hdt : dt ≠ 0) :
    taylorStep oneBodyProjector dt ∉ Matrix.unitaryGroup (Fin 2) ℂ := by
  intro hu
  have h := congrArg (fun A : Operator 2 => (A 0 0).re)
    (Matrix.mem_unitaryGroup_iff'.mp hu)
  simp [taylorStep, oneBodyProjector, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im] at h
  nlinarith [sq_pos_of_ne_zero hdt]

end Qatlib.Papers.ManyBodySim96.MainResults
