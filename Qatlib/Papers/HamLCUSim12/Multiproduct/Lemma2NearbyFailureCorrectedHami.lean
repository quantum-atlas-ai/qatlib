/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra
set_option warningAsError false

open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

theorem lemma2NearbyFailureCorrected : Lemma2NearbyFailureCorrected := by
  intro I _ _ κ hκ Ua Ub _hUa _hUb Δ _hΔ hbound ψ hψ
  rw [lemma2FailureProbCorrected_formula κ hκ]
  have hh := mul_le_mul_of_nonneg_left (hbound ψ hψ) (div_nonneg hκ (sq_nonneg (κ+1)))
  convert! hh using 1
  ring

end Qatlib.Papers.HamLCUSim12.Multiproduct
