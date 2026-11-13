/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Specification of resonance-aware noise variance

`ResonanceAwareNoiseVarianceCorrected` records the exact uniform-sequence variance of an affine
character-sum intensity at nonzero frequency. An indicator for 2y = 0 supplies the resonance
terms in the corrected form of the variance analysis associated with [Cornwell2014].

## Main statements

* `ResonanceAwareNoiseVarianceCorrected`: The exact centered affine-intensity variance
  b⁴(L²−L+δ(L²−L))+2b²L‖c‖²+2b²L · Re(c²)δ at nonzero frequency, where δ is one when 2y=0 and
  zero otherwise.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.AmpTransform.NoiseMoments

/-- The exact centered affine-intensity variance b⁴(L²−L+δ(L²−L))+2b²L‖c‖²+2b²L · Re(c²)δ at
nonzero frequency, where δ is one when 2y=0 and zero otherwise. -/
def ResonanceAwareNoiseVarianceCorrected : Prop :=
  ∀ (N L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ) (b : ℝ), y ≠ 0 →
    let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i*y)
    let μ := ‖c‖^2+b^2*(L : ℝ)
    let δ : ℝ := if 2*y=0 then 1 else 0
    ((N : ℝ)^L)⁻¹ * (∑ ω, (‖c+(b : ℂ)*S ω‖^2-μ)^2) =
      b^4*((L : ℝ)^2-L+δ*((L : ℝ)^2-L)) +
      2*b^2*(L : ℝ)*‖c‖^2 + 2*b^2*(L : ℝ)*(c^2).re*δ
end Qatlib.Concepts.AmpTransform.NoiseMoments
