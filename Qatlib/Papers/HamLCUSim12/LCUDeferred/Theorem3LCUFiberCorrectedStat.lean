/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix

def Theorem3LCUFiberCorrected : Prop :=
  ∀ (k : ℕ) (I : Type) [Fintype I] [DecidableEq I], 1 ≤ k →
    ∀ (U : Fin (k+1) → Matrix I I ℂ), (∀ q, U q ∈ Matrix.unitaryGroup I ℂ) →
      ∀ (c : Fin (k+1) → ℝ), (∀ q, c q ≠ 0) → (∃ q, 0 < c q) → (∃ q, c q < 0) →
        ∀ ψ : QState I, ∀ x : I,
          cwOutputCorrected k c U ψ (cwZero k, x)
            = (((∑ q, c q • U q)) *ᵥ ψ) x / (∑ q, |c q|)

end Qatlib.Papers.HamLCUSim12.LCUDeferred
