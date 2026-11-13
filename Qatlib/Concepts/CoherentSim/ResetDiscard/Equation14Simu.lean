/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation14Stat
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# Amplification of a scaled block encoding

`equation14` expresses the selected-fiber action of oblivious amplification for a block encoding
with scale `s`. The result is the scaled cubic operator appearing in Eq. (14) of
[BerryEtAl2015Taylor].

## Main statements

* `equation14`: The cubic selected-fiber formula for a scaled encoding.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- The selected-fiber action of an amplified scale-`s` block encoding of `U` equals the
embedded action of `(3 / s) • U - (4 / s³) • (U * Uᴴ * U)`. See [BerryEtAl2015Taylor]. -/
theorem equation14 : Equation14 := by
  intro J I _ _ _ _ W j₀ U s hW ψ
  have h := projected_obliviousAmplitudeAmplification_blockEncoding W j₀ U s hW
  have hv := congrArg (fun M : Matrix (J × I) (J × I) ℂ =>
    M *ᵥ TensorState (Ket j₀) ψ) h
  simpa only [← Matrix.mulVec_mulVec, fiberProjector_mulVec_tensorState_ket,
    fiberEmbed_mulVec_tensorState_ket] using hv

end Qatlib.Concepts.CoherentSim.ResetDiscard
