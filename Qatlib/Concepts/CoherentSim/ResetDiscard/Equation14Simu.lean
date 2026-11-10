/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation14Stat
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

theorem equation14 : Equation14 := by
  intro J I _ _ _ _ W j₀ U s hW ψ
  have h := projected_obliviousAmplitudeAmplification_blockEncoding W j₀ U s hW
  have hv := congrArg (fun M : Matrix (J × I) (J × I) ℂ =>
    M *ᵥ TensorState (Ket j₀) ψ) h
  simpa only [← Matrix.mulVec_mulVec, fiberProjector_mulVec_tensorState_ket,
    fiberEmbed_mulVec_tensorState_ket] using hv

end Qatlib.Concepts.CoherentSim.ResetDiscard
