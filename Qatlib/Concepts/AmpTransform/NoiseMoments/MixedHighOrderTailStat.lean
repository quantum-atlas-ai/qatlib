/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Specification of higher noise-intensity tails

`MixedHighOrderTail` states fourth-moment and deviation bounds for centered affine character-sum
intensity under uniform noise sampling. It uses the variance correction for nonzero frequencies
satisfying 2y = 0, refining the noise-moment setting of [Cornwell2014].

## Main statements

* `MixedHighOrderTail`: The contract bounding the centered affine intensity's fourth moment by
  the stated uniform magnitude factor times its resonance-corrected variance, and its tail at t
  > 0 by that variance divided by t².

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

/-- The contract bounding the centered affine intensity's fourth moment by the stated uniform
magnitude factor times its resonance-corrected variance, and its tail at t > 0 by that
variance divided by t². -/
def MixedHighOrderTail : Prop :=
  ∀ (N L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ) (b : ℝ), y ≠ 0 →
    let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i * y)
    let μ : ℝ := ‖c‖ ^ 2 + b ^ 2 * (L : ℝ)
    let X := fun ω : Fin L → ZMod N => ‖c + (b : ℂ) * S ω‖ ^ 2 - μ
    let delta : ℝ := if 2 * y = 0 then 1 else 0
    let var : ℝ :=
      b ^ 4 * ((L : ℝ) ^ 2 - (L : ℝ) + delta * ((L : ℝ) ^ 2 - (L : ℝ))) +
      2 * b ^ 2 * (L : ℝ) * ‖c‖ ^ 2 + 2 * b ^ 2 * (L : ℝ) * (c ^ 2).re * delta
    let bound : ℝ := ((‖c‖ + |b| * (L : ℝ)) ^ 2 + |μ|) ^ 2
    (((N : ℝ) ^ L)⁻¹ * (∑ ω, (X ω) ^ 4) ≤ bound * var) ∧
    ∀ t : ℝ, 0 < t →
      ((N : ℝ) ^ L)⁻¹ * (∑ ω, if t ≤ |X ω| then (1 : ℝ) else 0) ≤ var / t ^ 2

end Qatlib.Concepts.AmpTransform.NoiseMoments
