/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PairingModel01.MainResults.StepCount

@[expose] public section

/-!
# Cost of the pairing-model spectrum sweep

The spectrum measurement section multiplies the per-step logical gate
polynomial by the stated half-quadratic evolution step budget. The
result is a rational model for the cost described in the paper.
-/

set_option autoImplicit false

open Qatlib.Papers.PairingModel01.MainResults

namespace Qatlib.Papers.PairingModel01.MainResults

/-- Multiply the single-step gate polynomial by the spectrum sweep's
half-quadratic number of evolution steps. -/
def pairingSpectrumSteps (k N : ℕ) : ℚ :=
  (k : ℚ) ^ 2 * pairingStepCount N / 2

/-- The spectrum sweep cost is quadratic in its step parameter and
quartic in the number of pairing modes. -/
theorem pairing_spectrum_steps_le (k N : ℕ) (hN : 1 ≤ N) :
    pairingSpectrumSteps k N ≤ 5 * (k : ℚ) ^ 2 * (N : ℚ) ^ 4 := by
  unfold pairingSpectrumSteps
  calc
    _ ≤ (k : ℚ) ^ 2 * (10 * (N : ℚ) ^ 4) / 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pairingStepCount_le_ten N hN) (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

end Qatlib.Papers.PairingModel01.MainResults
