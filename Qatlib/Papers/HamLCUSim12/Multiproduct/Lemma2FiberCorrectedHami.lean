/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2FiberCorrectedStat
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

theorem lemma2FiberCorrected : Lemma2FiberCorrected := by
  intro I _ _ κ hκ Ua Ub _hUa _hUb ψ
  exact lemma2OutputCorrected_formula κ hκ Ua Ub ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
