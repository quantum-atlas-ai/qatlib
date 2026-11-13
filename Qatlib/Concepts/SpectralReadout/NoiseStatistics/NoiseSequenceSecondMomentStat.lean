/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Specification of noise-sequence second moments

This module defines `NoiseSequenceSecondMoment`, a proposition specifying uniform second moments
of finite sums of nontrivial cyclic characters. It records the moment identities used in the
noise-intensity analysis of [Cornwell2014].

The specification includes both the mean squared norm of a length-`L` character sum and the
squared norm after a fixed complex shift and real scaling.

## Main statements

* `NoiseSequenceSecondMoment`: the identities `E‖S‖² = L` and `E‖c+b*S‖² = ‖c‖²+b²*L` for
  uniform tuples and nonzero frequency.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
open scoped Classical
namespace Qatlib.Concepts.SpectralReadout.NoiseStatistics

/-- The proposition that uniform length-`L` character sums at nonzero frequency have second
moment `L`, and that adding a complex shift after real scaling gives second moment
`‖c‖^2+b^2*L`. -/
def NoiseSequenceSecondMoment : Prop :=
  ∀ (N L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ) (b : ℝ), y ≠ 0 →
    let S := fun ω : Fin L → ZMod N => ∑ i, ZMod.stdAddChar (ω i*y)
    ((N : ℝ)^L)⁻¹ * (∑ ω, ‖S ω‖^2) = (L : ℝ) ∧
    ((N : ℝ)^L)⁻¹ * (∑ ω, ‖c+(b : ℂ)*S ω‖^2) = ‖c‖^2+b^2*(L : ℝ)
end Qatlib.Concepts.SpectralReadout.NoiseStatistics
