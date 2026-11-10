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

def Theorem3LCUFailureCorrected : Prop :=
  ∀ (k : ℕ) (I : Type) [Fintype I] [DecidableEq I], 1 ≤ k →
    ∀ (U : Fin (k+1) → Matrix I I ℂ), (∀ q, U q ∈ Matrix.unitaryGroup I ℂ) →
      ∀ (c : Fin (k+1) → ℝ), (∀ q, c q ≠ 0) → (∃ q, 0 < c q) → (∃ q, c q < 0) →
        ∀ Δ : ℝ, 0 ≤ Δ →
          (∀ q q' : Fin (k+1), ∀ φ : QState I, Normalized φ →
            (∑ x : I, ‖((U q - U q') *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
          ∀ ψ : QState I, Normalized ψ →
            cwFailureProbCorrected k c U ψ ≤
              (k : ℝ) * Δ ^ 2 / 4
                + 4 * ((∑ q, if 0 < c q then c q else 0) / (∑ q, if c q < 0 then |c q| else 0))
                    / ((∑ q, if 0 < c q then c q else 0) / (∑ q, if c q < 0 then |c q| else 0)
                      + 1) ^ 2

end Qatlib.Papers.HamLCUSim12.LCUDeferred
