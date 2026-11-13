/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument

/-!
# Singlet teleportation conventions

The singlet state `singletResource` determines a preparation frame and branch Kraus operators
for the teleportation circuit. `singletSwap` and `singletSign` specify the outcome relabeling
and phase used in `singletCorrection`. The singlet convention follows the qubit protocol of
[BennettEtAl1993Teleportation].

## Main statements

* `singletResource`: The singlet vector `(|01⟩ - |10⟩) / √2`, indexed by pairs of Boolean
  values.
* `singletBranchKraus`: The input-to-output matrix for outcome `o` after singlet preparation and
  application of `teleportDecodeGate`.
* `singletCorrection`: The standard teleportation correction at the complemented outcome, scaled
  by `singletSign o`.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw

/-- The singlet vector `(|01⟩ - |10⟩) / √2`, indexed by pairs of Boolean values. -/
noncomputable def singletResource : QState (Bool × Bool) :=
  fun x => if x = (false, true) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if x = (true, false) then -((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The preparation matrix that tensors the input qubit with `singletResource` in the
teleportation register ordering. -/
noncomputable def singletPreparedFrame : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
      then singletResource ((teleportRegisterEquiv.symm r).1.2,
        (teleportRegisterEquiv.symm r).2)
      else 0

/-- The input-to-output matrix for outcome `o` after singlet preparation and application of
`teleportDecodeGate`. -/
noncomputable def singletBranchKraus (o : Bool × Bool) : Operator 2 :=
  Matrix.of fun c i =>
    (teleportDecodeGate * singletPreparedFrame)
      (teleportRegisterEquiv ((o.1, o.2), boolEquivFin2.symm c)) i

/-- The teleportation outcome relabeling that complements both Boolean coordinates. -/
def singletSwap (o : Bool × Bool) : Bool × Bool := (!o.1, !o.2)

/-- The phase factor equal to `-1` when the second outcome bit is true and `1` otherwise. -/
def singletSign (o : Bool × Bool) : ℂ := if o.2 then -1 else 1

/-- The standard teleportation correction at the complemented outcome, scaled by `singletSign
o`. -/
noncomputable def singletCorrection (o : Bool × Bool) : Operator 2 :=
  singletSign o • teleportCorrection (singletSwap o)
end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
