/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.CostRestrictedSubgoalStat
set_option warningAsError false

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

theorem costRestrictedSubgoal : CostRestrictedSubgoal := by
  intro κ ε hκ hε M hM
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  refine ⟨one_div_pos.mpr (pow_pos hκpos 2), ?_⟩
  have hκε : 0 < κ / ε := div_pos hκpos hε
  have hMpos : (0 : ℝ) < M := hκε.trans_le hM
  have h : (M : ℝ)⁻¹ ≤ (κ / ε)⁻¹ := (inv_le_inv₀ hMpos hκε).mpr hM
  rwa [inv_div] at h

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
