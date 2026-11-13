/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation11Stat
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Projected LCU workspace action

`equation11` proves the projected action of an LCU workspace built from unitary summands and a
scaled nonnegative preparation. The selected ancillary fiber contains the weighted operator sum
divided by its preparation scale, as in Eq. (11) of [BerryEtAl2015Taylor].

## Main statements

* `equation11`: The projected LCU workspace identity.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- The selected ancillary projection of the LCU workspace acting on an embedded vector equals
the embedded weighted operator sum, scaled by the inverse preparation scale. See
[BerryEtAl2015Taylor]. -/
theorem equation11 : Equation11 := by
  intro J I _ _ _ _ U hU w hw P s j₀ hP ψ
  have hencoding := lcu_isBlockEncoding_of_isScaledPrepare U hU hw hP
  have h := (isProjectedEncoding_iff_isBlockEncoding _ _ _ _).mpr hencoding
  have hv := congrArg (fun M : Matrix (J × I) (J × I) ℂ =>
    M *ᵥ TensorState (Ket j₀) ψ) h.2.2
  simpa only [← Matrix.mulVec_mulVec, fiberProjector_mulVec_tensorState_ket,
    fiberEmbed_mulVec_tensorState_ket] using hv

end Qatlib.Concepts.CoherentSim.ResetDiscard
