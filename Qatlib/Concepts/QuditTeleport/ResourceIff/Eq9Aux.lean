/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.ResourceIff

open Matrix

noncomputable def eq9Resource (u v p q : QState (Fin 2)) : QState (Fin 2 × Fin 2) :=
  fun x => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (u x.1 * p x.2 + v x.1 * q x.2)

def eq9OrthoPairs (u v p q : QState (Fin 2)) : Prop :=
  Normalized u ∧ Normalized v ∧ Normalized p ∧ Normalized q ∧
    Inner u v = 0 ∧ Inner p q = 0

noncomputable def eq9ResourceB (u v p q : QState Bool) : QState (Bool × Bool) :=
  fun x => ((1 / Real.sqrt 2 : ℝ) : ℂ) * (u x.1 * p x.2 + v x.1 * q x.2)

def eq9OrthoPairsB (u v p q : QState Bool) : Prop :=
  Normalized u ∧ Normalized v ∧ Normalized p ∧ Normalized q ∧
    Inner u v = 0 ∧ Inner p q = 0

noncomputable def eq9PreparedFrame (u v p q : QState Bool) : Matrix (Fin 8) (Fin 2) ℂ :=
  Matrix.of fun r i =>
    if (teleportRegisterEquiv.symm r).1.1 = boolEquivFin2.symm i
      then eq9ResourceB u v p q ((teleportRegisterEquiv.symm r).1.2,
        (teleportRegisterEquiv.symm r).2)
      else 0

noncomputable def eq9BranchKraus (u v p q : QState Bool) (o : Bool × Bool) : Operator 2 :=
  Matrix.of fun c i =>
    (teleportDecodeGate * eq9PreparedFrame u v p q)
      (teleportRegisterEquiv ((o.1, o.2), boolEquivFin2.symm c)) i

noncomputable def bobFirstEquiv :
    (Fin 2 × Fin 2) × Fin 2 ≃ (Fin 2 × Fin 4) :=
  (Equiv.prodComm (Fin 2 × Fin 2) (Fin 2)).trans
    (Equiv.prodCongr (Equiv.refl (Fin 2)) (finProdFinEquiv (m := 2) (n := 2)))

noncomputable def bobBranchMarginal
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (s : Fin 4) (ρ : Operator 2) : Operator 2 :=
  PartialTrace (relabelGate bobFirstEquiv
    ((TensorGate (K s) (1 : Operator 2)) *
      (relabelGate (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)).symm
        (TensorGate ρ ω)) *
      (TensorGate (K s) (1 : Operator 2))ᴴ))

def FourFixedCorrectionsTeleport
    (K : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ω : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  (∀ s : Fin 4, U s ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  (∑ s : Fin 4, (TensorGate (K s) (1 : Operator 2))ᴴ
      * TensorGate (K s) (1 : Operator 2) = 1) ∧
  ∀ ρ : Operator 2,
    ∑ s : Fin 4, (U s) * bobBranchMarginal K ω s ρ * (U s)ᴴ = ρ

end Qatlib.Concepts.QuditTeleport.ResourceIff
