/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationTargetStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout

namespace Qatlib.Concepts.RiskEstimation.PolyRotation

theorem riskPolyRotationTarget : PolyRotationTarget := by
  intro c y hc hc1 hy0 hy1
  have hs0 : 0 ≤ c * (y - 1 / 2) + 1 / 2 := by nlinarith
  have hs1 : c * (y - 1 / 2) + 1 / 2 ≤ 1 := by nlinarith
  have hroot0 := Real.sqrt_nonneg (c * (y - 1 / 2) + 1 / 2)
  have hroot1 : Real.sqrt (c * (y - 1 / 2) + 1 / 2) ≤ 1 := Real.sqrt_le_one.mpr hs1
  have hangle : c * riskArcsineTarget c y + Real.pi / 4 =
      Real.arcsin (Real.sqrt (c * (y - 1 / 2) + 1 / 2)) := by
    unfold riskArcsineTarget
    field_simp [hc.ne']
    ring
  rw [hangle, Real.sin_arcsin (by linarith) hroot1, Real.sq_sqrt hs0]

end Qatlib.Concepts.RiskEstimation.PolyRotation
