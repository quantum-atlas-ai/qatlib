/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

/-!
# Auxiliary LCU qubitization projection statement

The proposition `ObliviousAmplificationSubgoal` specifies a reference-fiber projection identity
for a prepared LCU of Hermitian unitaries. It states the factor 2x² − 1 on normalized
eigenstates of the weighted sum and serves as an auxiliary qubitization statement. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `ObliviousAmplificationSubgoal`: The proposition that the qubitization output for a prepared
  nonnegative LCU of Hermitian unitaries projects onto the reference fiber as (2x² − 1) times a
  normalized input eigenstate tensored with that fiber.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

open Matrix

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The proposition that the qubitization output for a prepared nonnegative LCU of Hermitian
unitaries projects onto the reference fiber as (2x² − 1) times a normalized input eigenstate
tensored with that fiber. -/
def ObliviousAmplificationSubgoal : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ), (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) →
    (∀ j, (U j)ᴴ = U j) →
    ∀ (w : J → ℝ), (∀ j, 0 ≤ w j) →
    ∀ (P : Matrix J J ℂ) (j₀ : J), IsPrepare P w j₀ →
    ∀ (ψ : QState I), Normalized ψ →
    ∀ (x : ℝ), (∑ j, w j • U j) *ᵥ ψ = ((x : ℝ) : ℂ) • ψ →
    FiberProjector j₀ *ᵥ (QubitizationWalk (LCUWorkspace U P) j₀ *ᵥ
        TensorState (Ket j₀) ψ)
      = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • TensorState (Ket j₀) ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
