/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation11Stat
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Tensor
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

theorem equation11 : Equation11 := by
  intro J I _ _ _ _ U hU w hw P s j₀ hP ψ
  have hencoding := lcu_isBlockEncoding_of_isScaledPrepare U hU hw hP
  have h := (isProjectedEncoding_iff_isBlockEncoding _ _ _ _).mpr hencoding
  have hv := congrArg (fun M : Matrix (J × I) (J × I) ℂ =>
    M *ᵥ TensorState (Ket j₀) ψ) h.2.2
  simpa only [← Matrix.mulVec_mulVec, fiberProjector_mulVec_tensorState_ket,
    fiberEmbed_mulVec_tensorState_ket] using hv

end Qatlib.Concepts.CoherentSim.ResetDiscard
