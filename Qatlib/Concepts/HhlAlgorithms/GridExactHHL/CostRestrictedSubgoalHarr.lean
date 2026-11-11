/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.CostRestrictedSubgoalStat

/-!
# Resolution bounds for the restricted HHL model

This module proves `CostRestrictedSubgoal`, the elementary inequalities relating grid size,
error tolerance, and the spectral bound parameter. These inequalities provide numerical
prerequisites for the restricted linear-system setting inspired by [HarrowHassidimLloyd2009].

## Main statements

* `costRestrictedSubgoal`: positivity of the inverse-square bound and the grid-resolution
  inequality.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

/-- For `κ ≥ 1`, positive `ε`, and grid size `M ≥ κ / ε`, the quantity `1 / κ²` is positive and
`M⁻¹ ≤ ε / κ`. -/
theorem costRestrictedSubgoal : CostRestrictedSubgoal := by
  intro κ ε hκ hε M hM
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  refine ⟨one_div_pos.mpr (pow_pos hκpos 2), ?_⟩
  have hκε : 0 < κ / ε := div_pos hκpos hε
  have hMpos : (0 : ℝ) < M := hκε.trans_le hM
  have h : (M : ℝ)⁻¹ ≤ (κ / ε)⁻¹ := (inv_le_inv₀ hMpos hκε).mpr hM
  rwa [inv_div] at h

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
