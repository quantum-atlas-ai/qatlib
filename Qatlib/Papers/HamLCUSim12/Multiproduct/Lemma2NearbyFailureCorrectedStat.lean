/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions

/-!
# Corrected nearby-unitary failure statement

The proposition `Lemma2NearbyFailureCorrected` records the proximity-dependent failure bound for
`lemma2FailureProbCorrected`. It uses a uniform bound on the action of `Ua - Ub` on normalized
states and concludes the same bound for every normalized input to the circuit. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `Lemma2NearbyFailureCorrected`: The proposition bounding corrected LCU failure by κΔ²/(κ + 1)²
  for κ, Δ ≥ 0 and unitary inputs satisfying the uniform squared-norm difference bound Δ².

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix

/-- The proposition bounding corrected LCU failure by κΔ²/(κ + 1)² for κ, Δ ≥ 0 and unitary
inputs satisfying the uniform squared-norm difference bound Δ². -/
def Lemma2NearbyFailureCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ Δ : ℝ, 0 ≤ Δ →
        (∀ φ : QState I, Normalized φ → (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
        ∀ ψ : QState I, Normalized ψ →
          lemma2FailureProbCorrected κ Ua Ub ψ ≤ κ * Δ ^ 2 / (κ + 1) ^ 2

end Qatlib.Papers.HamLCUSim12.Multiproduct
