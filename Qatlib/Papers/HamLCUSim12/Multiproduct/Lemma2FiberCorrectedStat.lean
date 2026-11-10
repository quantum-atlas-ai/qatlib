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

def Lemma2FiberCorrected : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (κ : ℝ), 0 ≤ κ →
    ∀ (Ua Ub : Matrix I I ℂ), Ua ∈ Matrix.unitaryGroup I ℂ → Ub ∈ Matrix.unitaryGroup I ℂ →
      ∀ ψ : QState I,
        (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _ => false, x)
            = ((((κ : ℂ) / (κ + 1)) • Ua + (((1 : ℂ) / (κ + 1)) • Ub)) *ᵥ ψ) x)
        ∧ (∀ x : I, lemma2OutputCorrected κ Ua Ub ψ (fun _ => true, x)
            = (((((Real.sqrt κ / (κ + 1) : ℝ) : ℂ)) • (Ub - Ua)) *ᵥ ψ) x)

end Qatlib.Papers.HamLCUSim12.Multiproduct
