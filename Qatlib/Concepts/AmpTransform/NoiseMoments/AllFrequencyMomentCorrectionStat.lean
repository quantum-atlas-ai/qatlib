/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Specification of all-frequency noise moments

`AllFrequencyMomentCorrection` distinguishes the deterministic character sum at zero frequency
from the centered random sum at nonzero frequency. It states the corresponding second moments
and affine-intensity means for the uniform-sequence noise model used with [Cornwell2014].

## Main statements

* `AllFrequencyMomentCorrection`: The all-frequency moment contract: at y=0 the character-sum
  intensity is L² and the affine intensity is ‖c+bL‖², while at y≠0 their means are L and
  ‖c‖²+b²L.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

/-- The all-frequency moment contract: at y=0 the character-sum intensity is L² and the affine
intensity is ‖c+bL‖², while at y≠0 their means are L and ‖c‖²+b²L. -/
def AllFrequencyMomentCorrection : Prop :=
  ∀ (N L : ℕ) [NeZero N] (c : ℂ) (b : ℝ),
    ∀ y : ZMod N,
      let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i * y)
      (y = 0 →
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖S ω‖ ^ 2) = (L : ℝ) ^ 2 ∧
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖c + (b : ℂ) * S ω‖ ^ 2) = ‖c + (b : ℂ) * (L : ℂ)‖ ^ 2) ∧
      (y ≠ 0 →
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖S ω‖ ^ 2) = (L : ℝ) ∧
        ((N : ℝ) ^ L)⁻¹ * (∑ ω, ‖c + (b : ℂ) * S ω‖ ^ 2) = ‖c‖ ^ 2 + b ^ 2 * (L : ℝ))

end Qatlib.Concepts.AmpTransform.NoiseMoments
