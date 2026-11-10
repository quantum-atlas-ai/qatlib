/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCrudeCorrectedStat
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

theorem lemma2NearbyFailureCrudeCorrected : Lemma2NearbyFailureCrudeCorrected := by
  intro I _ _ κ hκ Ua Ub hUa hUb ψ hψ
  have hh := lemma2NearbyFailureCorrected I κ hκ Ua Ub hUa hUb 2 (by norm_num)
    (fun φ hφ=>by norm_num; exact nearby_unitary_difference_sq Ua Ub hUa hUb φ hφ) ψ hψ
  norm_num at hh ⊢
  simpa only [mul_comm] using hh

end Qatlib.Papers.HamLCUSim12.Multiproduct
