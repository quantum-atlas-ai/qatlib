/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.RankOneOpNorm
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped Matrix Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable abbrev rankOneProj (u : I → ℂ) : Matrix I I ℂ := rankOne u

noncomputable abbrev phaseDistance (u v : I → ℂ) : ℝ := phaseDist u v

theorem rankOneProj_norm_sub_eq {u v : I → ℂ} (hu : l2norm u = 1) (hv : l2norm v = 1) :
    ‖rankOneProj u - rankOneProj v‖ = Real.sqrt (1 - l2abs u v ^ 2) :=
  opNorm_rankOne_sub hu hv

theorem sqrt_one_sub_sq_le_sqrt_two_sub_two (c : ℝ) (_h0 : 0 ≤ c) (_h1 : c ≤ 1) :
    Real.sqrt (1 - c ^ 2) ≤ Real.sqrt (2 - 2 * c) := by
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (1 - c)]

theorem rankOneProj_norm_sub_le_phaseDistance {u v : I → ℂ} (hu : l2norm u = 1)
    (hv : l2norm v = 1) :
    ‖rankOneProj u - rankOneProj v‖ ≤ phaseDistance u v :=
  (opNorm_rankOne_sub hu hv).le.trans (sqrt_le_phaseDist hu hv)

theorem complementaryProjector_norm_sub_le {u v : I → ℂ} (hu : l2norm u = 1)
    (hv : l2norm v = 1) {e : ℝ} (he : phaseDistance u v ≤ e) :
    ‖(1 - rankOneProj u) - (1 - rankOneProj v)‖ ≤ e :=
  (mixerGen_diff_le hu hv).trans he

end Qatlib.Papers.ProjectorQAOA26.StageStability
