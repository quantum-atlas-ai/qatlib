/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Statement of the projected LCU identity

`Equation11` states the selected-fiber action of the LCU workspace for nonnegative weights and a
scaled preparation matrix. It isolates the projected identity used in Eq. (11) of
[BerryEtAl2015Taylor].

## Main statements

* `Equation11`: The proposition specifying the projected weighted operator sum.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- The proposition that a scaled nonnegative preparation and unitary summands yield the
selected-fiber LCU action equal to the weighted operator sum divided by the preparation
scale. -/
def Equation11 : Prop :=
  ∀ (J I : Type*) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ), (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
    ∀ (w : J → ℝ), (∀ j, 0 ≤ w j) →
    ∀ (P : Matrix J J ℂ) (s : ℝ) (j₀ : J), IsScaledPrepare P w s j₀ →
    ∀ (ψ : QState I),
    FiberProjector j₀ *ᵥ (LCUWorkspace U P *ᵥ TensorState (Ket j₀) ψ) =
      TensorState (Ket j₀) ((((s⁻¹ : ℝ) : ℂ) • (∑ j, w j • U j)) *ᵥ ψ)

end Qatlib.Concepts.CoherentSim.ResetDiscard
