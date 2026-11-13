/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweightingCore
import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweighting
import Qatlib.Concepts.NativeNumerics.WaterFilling
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Rational Fourier clipping profiles

Defines rational Fourier-magnitude and flat-target profiles together with their real clipped
profile. The clipping agrees with `levelFill`, and in the two-bit case with target amplitude one
half it agrees with `bhspEps`. See [OzolsRoettelerRoland2013].

## Main statements

* `bhspClipQ_identification`: identifies the rational-data clipping with level filling.
* `bhspClipQ_eq_bhspEps`: specializes the clipping to the two-bit profile.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib.Concepts.Waterfill.LevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Papers.RejectSample11.MainResults

set_option autoImplicit false

open Matrix
open Qatlib
open scoped BigOperators ComplexOrder ENNReal

variable {m : ℕ}

/-- The rational profile of absolute Fourier coefficients `|fHat w|`. -/
def bhspPiQ {n : ℕ} (fHat : Fin (2 ^ n) → ℚ) : Fin (2 ^ n) → ℚ := fun w => |fHat w|

/-- The constant rational target profile with value `c` on `Fin m`. -/
def flatSigmaQ (m : ℕ) (c : ℚ) : Fin m → ℚ := fun _ => c

/-- The real clipped Fourier profile `min |(fHat w : ℝ)| (γ * (c : ℝ))`. -/
def bhspClipQ {n : ℕ} (fHat : Fin (2 ^ n) → ℚ) (c : ℚ) (γ : ℝ) : Fin (2 ^ n) → ℝ :=
  fun w => min |(fHat w : ℝ)| (γ * (c : ℝ))

/-- The clipped Fourier profile equals the level-filled profile of the rational magnitudes and
flat target at every index. -/
theorem bhspClipQ_identification {n : ℕ} (fHat : Fin (2 ^ n) → ℚ) (c : ℚ) (γ : ℝ)
    (w : Fin (2 ^ n)) :
    bhspClipQ fHat c γ w = levelFill (bhspPiQ fHat) (flatSigmaQ _ c) γ w := by
  unfold bhspClipQ bhspPiQ flatSigmaQ levelFill
  rw [Rat.cast_abs]

/-- When `n = 2` and the target amplitude is one half, the rational-data clipped profile equals
`bhspEps` after casting Fourier coefficients to real numbers. -/
theorem bhspClipQ_eq_bhspEps {n : ℕ} (h2 : n = 2) (fHat : Fin (2 ^ n) → ℚ) (γ : ℝ)
    (w : Fin (2 ^ n)) :
    bhspClipQ fHat (1 / 2 : ℚ) γ w = bhspEps (fun x => (fHat x : ℝ)) γ w := by
  subst h2
  have hbeta : (fun x : Fin (2 ^ 2) => (fHat x : ℝ)) w = (fHat w : ℝ) := rfl
  have hdiv : ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  have hsqrt : Real.sqrt ((2 : ℝ) ^ 2) = 2 := Real.sqrt_sq (by norm_num)
  have hscale : γ * ((1 / 2 : ℚ) : ℝ) = γ / Real.sqrt ((2 : ℝ) ^ 2) := by
    rw [hdiv, hsqrt]
    ring
  unfold bhspClipQ bhspEps
  rw [hbeta, hscale]

end Qatlib.Papers.RejectSample11.MainResults
