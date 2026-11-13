/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra

/-!
# Failure bound for corrected nearby-unitary LCU

This module proves `lemma2NearbyFailureCorrected`, bounding the corrected circuit's failure
probability by κΔ²/(κ + 1)². The hypothesis bounds the squared norm of the difference of the two
unitaries on every normalized state by Δ². See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `lemma2NearbyFailureCorrected`: For κ ≥ 0 and unitary inputs whose difference has squared norm
  at most Δ² on normalized states, the corrected failure probability is at most κΔ²/(κ + 1)² on
  every normalized input.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- For κ ≥ 0 and unitary inputs whose difference has squared norm at most Δ² on normalized
states, the corrected failure probability is at most κΔ²/(κ + 1)² on every normalized input.
See [ChildsWiebe2012]. -/
theorem lemma2NearbyFailureCorrected : Lemma2NearbyFailureCorrected := by
  intro I _ _ κ hκ Ua Ub _hUa _hUb Δ _hΔ hbound ψ hψ
  rw [lemma2FailureProbCorrected_formula κ hκ]
  have hh := mul_le_mul_of_nonneg_left (hbound ψ hψ) (div_nonneg hκ (sq_nonneg (κ+1)))
  convert! hh using 1
  ring

end Qatlib.Papers.HamLCUSim12.Multiproduct
