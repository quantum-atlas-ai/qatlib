/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix

def Lemma2NearbyFailureCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ Δ : ℝ, 0 ≤ Δ →
        (∀ φ : QState I, Normalized φ → (∑ x : I, ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
        ∀ ψ : QState I, Normalized ψ →
          lemma2FailureProbCorrected κ Ua Ub ψ ≤ κ * Δ ^ 2 / (κ + 1) ^ 2

end Qatlib.Papers.HamLCUSim12.Multiproduct
