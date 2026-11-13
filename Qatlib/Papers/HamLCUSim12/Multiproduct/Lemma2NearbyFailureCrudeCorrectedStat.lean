/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions

/-!
# Uniform corrected LCU failure statement

The proposition `Lemma2NearbyFailureCrudeCorrected` specifies the upper bound 4κ/(κ + 1)² for
`lemma2FailureProbCorrected`. It quantifies over all finite systems, nonnegative κ, unitary
input matrices, and normalized states. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `Lemma2NearbyFailureCrudeCorrected`: The proposition that the corrected two-unitary LCU
  failure probability is at most 4κ/(κ + 1)² for κ ≥ 0, unitary inputs, and every normalized
  state.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix

/-- The proposition that the corrected two-unitary LCU failure probability is at most 4κ/(κ +
1)² for κ ≥ 0, unitary inputs, and every normalized state. -/
def Lemma2NearbyFailureCrudeCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I, Normalized ψ →
        lemma2FailureProbCorrected κ Ua Ub ψ ≤ 4 * κ / (κ + 1) ^ 2

end Qatlib.Papers.HamLCUSim12.Multiproduct
