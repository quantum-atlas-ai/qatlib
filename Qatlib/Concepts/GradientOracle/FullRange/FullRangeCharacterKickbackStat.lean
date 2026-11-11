/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueGradient

/-!
# Full-range character kickback specification

`FullRangeCharacterKickback` states that the character state on `ZMod (2 ^ (K + k))` is
normalized and prepared by an inverse QFT. It also requires a unitary value oracle and the exact
tensor-state phase-kickback identity for every finite input type. See [Jordan2005Gradient] for
background.

## Main statements

* `FullRangeCharacterKickback`: The proposition combining normalization and inverse-QFT
  preparation of the full-range character state with value-oracle unitarity and its exact
  phase-kickback identity.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical

/-- The proposition combining normalization and inverse-QFT preparation of the full-range
character state with value-oracle unitarity and its exact phase-kickback identity. -/
def FullRangeCharacterKickback : Prop :=
  ∀ (K k : ℕ), Normalized (fullRangeKickState K k) ∧
    ApplyGate ((zmodQFTGate (N := 2^(K+k)))ᴴ) (Ket (fullRangeCharacterIndex K k)) =
      fullRangeKickState K k ∧
    ∀ (X : Type) [Fintype X] [DecidableEq X] (v : X → ZMod (2^(K+k))),
      gradientValueOracle (2^(K+k)) v ∈ Matrix.unitaryGroup (X × ZMod (2^(K+k))) ℂ ∧
      ∀ ψ : QState X,
        ApplyGate (gradientValueOracle (2^(K+k)) v) (TensorState ψ (fullRangeKickState K k)) =
          TensorState (ApplyGate (Matrix.diagonal (fun x =>
            Complex.exp (2*Real.pi*Complex.I*(fullRangePhase K k v x : ℂ)))) ψ)
            (fullRangeKickState K k)

end Qatlib.Concepts.GradientOracle.FullRange
