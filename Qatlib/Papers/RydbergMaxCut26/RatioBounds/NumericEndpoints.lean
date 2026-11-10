/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.RationalSOS
import Qatlib.Papers.RydbergMaxCut26.RatioBounds.ConditionalRatio
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Endpoints

theorem scalar_ratio_651 : (0.651:ℝ)≤Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.conditionalRatio 1 := by
  apply Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.ratio_651_of_bound
  intro t ht
  have h := Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS.hnum_651 t ht
  norm_num only [Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS.kernelConstant] at h ⊢
  exact h

theorem scalar_ratio_614 : (0.614:ℝ)≤Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.conditionalRatio 0.89 := by
  apply Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.ratio_614_of_bound
  intro t ht
  have ht' : t∈Set.Ico (-1:ℝ) ((89/100:ℝ)/3) := by norm_num at ht ⊢;exact ht
  have h := Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS.hnum_614 t ht'
  norm_num only [Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS.kernelConstant] at h ⊢
  exact h
end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Endpoints
