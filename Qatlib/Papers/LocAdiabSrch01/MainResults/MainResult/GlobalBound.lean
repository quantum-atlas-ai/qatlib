/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule.Spectrum
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Real

namespace Qatlib.Papers.LocAdiabSrch01.MainResults.MainResult

theorem global_adiabatic_condition
    {N ε gmin dHds T : ℝ} (hN : 0 < N) (hε : 0 < ε) (hT : 0 < T)
    (hgmin : gmin ^ 2 = 1 / N)
    (hdH : |dHds| ≤ 1)
    (hTN : N / ε ≤ T) :
    |dHds| / (T * gmin ^ 2) ≤ ε := by
  have hgpos : 0 < gmin ^ 2 := by rw [hgmin]; positivity
  have hTg : 0 < T * gmin ^ 2 := mul_pos hT hgpos
  have hNe : 0 < N := hN

  have hNT : N ≤ T * ε := (div_le_iff₀ hε).mp hTN

  have hge : 1 ≤ ε * (T * gmin ^ 2) := by
    rw [hgmin]
    have heq : ε * (T * (1 / N)) = T * ε / N := by field_simp
    rw [heq]
    rw [le_div_iff₀ hN]
    simpa using hNT

  rw [div_le_iff₀ hTg]
  linarith [hdH, hge]

end Qatlib.Papers.LocAdiabSrch01.MainResults.MainResult
