/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.DepolarizingLaw

noncomputable def singletResource : QState (Bool × Bool) :=
  fun x => if x = (false, true) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if x = (true, false) then -((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

noncomputable def singletPreparedFrame : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
      then singletResource ((teleportRegisterEquiv.symm r).1.2,
        (teleportRegisterEquiv.symm r).2)
      else 0

noncomputable def singletBranchKraus (o : Bool × Bool) : Operator 2 :=
  Matrix.of fun c i =>
    (teleportDecodeGate * singletPreparedFrame)
      (teleportRegisterEquiv ((o.1, o.2), boolEquivFin2.symm c)) i

def singletSwap (o : Bool × Bool) : Bool × Bool := (!o.1, !o.2)

def singletSign (o : Bool × Bool) : ℂ := if o.2 then -1 else 1

noncomputable def singletCorrection (o : Bool × Bool) : Operator 2 :=
  singletSign o • teleportCorrection (singletSwap o)
end Qatlib.Concepts.QuditTeleport.DepolarizingLaw
