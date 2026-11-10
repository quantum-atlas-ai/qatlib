/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9ResourceTeleportationStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix

structure Clause1Endpoint where

  u : QState Bool

  v : QState Bool

  p : QState Bool

  q : QState Bool

  ortho : eq9OrthoPairsB u v p q

  correctionUnitary : ∀ o : Bool × Bool,
    (((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ) ∈ Matrix.unitaryGroup (Fin 2) ℂ)

  restores : ∀ (o : Bool × Bool) (ρ : Operator 2),
    ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o) * ρ *
        ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o)ᴴ
      = (1 / 4 : ℂ) • ρ

def Clause1BranchCount : ℕ := Fintype.card (Bool × Bool)

noncomputable def Clause1RestoreWeight : ℂ := 1 / 4

end Qatlib.Papers.MeasureOnly00.TeleportBound
