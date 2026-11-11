/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCrudeCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra

/-!
# Uniform failure bound for corrected two-unitary LCU

This module proves `lemma2NearbyFailureCrudeCorrected`, the uniform upper bound 4κ/(κ + 1)² for
the corrected circuit's failure probability. It specializes the proximity-dependent estimate
using the squared-norm difference bound 4 for two unitaries acting on a normalized state. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `lemma2NearbyFailureCrudeCorrected`: For κ ≥ 0, two unitary inputs, and a normalized input
  state, the corrected LCU failure probability is at most 4κ/(κ + 1)².

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- For κ ≥ 0, two unitary inputs, and a normalized input state, the corrected LCU failure
probability is at most 4κ/(κ + 1)². See [ChildsWiebe2012]. -/
theorem lemma2NearbyFailureCrudeCorrected : Lemma2NearbyFailureCrudeCorrected := by
  intro I _ _ κ hκ Ua Ub hUa hUb ψ hψ
  have hh := lemma2NearbyFailureCorrected I κ hκ Ua Ub hUa hUb 2 (by norm_num)
    (fun φ hφ=>by norm_num; exact nearby_unitary_difference_sq Ua Ub hUa hUb φ hφ) ψ hψ
  norm_num at hh ⊢
  simpa only [mul_comm] using hh

end Qatlib.Papers.HamLCUSim12.Multiproduct
