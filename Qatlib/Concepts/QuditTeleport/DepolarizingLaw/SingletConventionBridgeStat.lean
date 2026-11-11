/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.DepolarizingLaw.SingletConventionBridgeAuxiliary

/-!
# The singlet convention bridge contract

`SingletConventionBridge` states the relation between singlet-prepared and standard
teleportation branches. It also requires each corrected singlet branch to act as one quarter of
the identity map. The singlet convention follows the qubit protocol of
[BennettEtAl1993Teleportation].

## Main statements

* `SingletConventionBridge`: The conjunction of the signed outcome-relabeling identity for
  singlet Kraus operators and exact recovery of one quarter of every input by each corrected
  branch.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw

open Matrix

/-- The conjunction of the signed outcome-relabeling identity for singlet Kraus operators and
exact recovery of one quarter of every input by each corrected branch. -/
def SingletConventionBridge : Prop :=
  (∀ o : Bool × Bool,
    singletBranchKraus o = singletSign o • teleportBranchKraus (singletSwap o)) ∧
  (∀ (ρ : Operator 2) (o : Bool × Bool),
    (singletCorrection o * singletBranchKraus o) * ρ *
      (singletCorrection o * singletBranchKraus o)ᴴ = (1 / 4 : ℂ) • ρ)

end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
