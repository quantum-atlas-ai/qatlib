/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.RankOneOpNorm

/-!
# Projector distances and phase distances

This module exposes `rankOneProj` and `phaseDistance` and relates them through the exact norm
formula for differences of normalized rank-one projectors. The resulting comparison also
controls complementary projectors, as in [ZhouAnLiu2026].

## Main statements

* `rankOneProj_norm_sub_eq`: For normalized vectors, the norm of the projector difference equals
  the square root of one minus their squared overlap magnitude, as in [Zhou et al., Lemma
  C.1][ZhouAnLiu2026].
* `rankOneProj_norm_sub_le_phaseDistance`: The norm of the projector difference for normalized
  vectors is at most their phase distance.
* `complementaryProjector_norm_sub_le`: A bound `e` on the phase distance between normalized
  vectors also bounds the norm distance between their complementary projectors.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped Matrix Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- An abbreviation for the rank-one operator `rankOne u`, which is a projector when `u` is
normalized. -/
noncomputable abbrev rankOneProj (u : I → ℂ) : Matrix I I ℂ := rankOne u

/-- An abbreviation for the phase-aligned vector distance `phaseDist u v`. -/
noncomputable abbrev phaseDistance (u v : I → ℂ) : ℝ := phaseDist u v

/-- For normalized vectors, the norm of the projector difference equals the square root of one
minus their squared overlap magnitude, as in [Zhou et al., Lemma C.1][ZhouAnLiu2026]. -/
theorem rankOneProj_norm_sub_eq {u v : I → ℂ} (hu : l2norm u = 1) (hv : l2norm v = 1) :
    ‖rankOneProj u - rankOneProj v‖ = Real.sqrt (1 - l2abs u v ^ 2) :=
  opNorm_rankOne_sub hu hv

/-- For `0 ≤ c ≤ 1`, the square root of `1 - c ^ 2` is at most the square root of `2 - 2 * c`. -/
theorem sqrt_one_sub_sq_le_sqrt_two_sub_two (c : ℝ) (_h0 : 0 ≤ c) (_h1 : c ≤ 1) :
    Real.sqrt (1 - c ^ 2) ≤ Real.sqrt (2 - 2 * c) := by
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (1 - c)]

/-- The norm of the projector difference for normalized vectors is at most their phase distance. -/
theorem rankOneProj_norm_sub_le_phaseDistance {u v : I → ℂ} (hu : l2norm u = 1)
    (hv : l2norm v = 1) :
    ‖rankOneProj u - rankOneProj v‖ ≤ phaseDistance u v :=
  (opNorm_rankOne_sub hu hv).le.trans (sqrt_le_phaseDist hu hv)

/-- A bound `e` on the phase distance between normalized vectors also bounds the norm distance
between their complementary projectors. -/
theorem complementaryProjector_norm_sub_le {u v : I → ℂ} (hu : l2norm u = 1)
    (hv : l2norm v = 1) {e : ℝ} (he : phaseDistance u v ≤ e) :
    ‖(1 - rankOneProj u) - (1 - rankOneProj v)‖ ≤ e :=
  (mixerGen_diff_le hu hv).trans he

end Qatlib.Papers.ProjectorQAOA26.StageStability
