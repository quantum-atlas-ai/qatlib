/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9ResourceTeleportationStat

/-!
# Teleportation endpoint data

`Clause1Endpoint` packages four resource vectors satisfying `eq9OrthoPairsB`, unitary
corrections for all two-bit branches, and restoration of each input operator with weight one
quarter. `Clause1BranchCount` and `Clause1RestoreWeight` name the branch count and common
restoration weight. The measurement-only computation context is [RaussendorfBriegel2000].

## Main statements

* `Clause1Endpoint`: resource data with branch correction and restoration proofs.
* `Clause1BranchCount`: cardinality of the two-bit outcome type.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix

/-- Resource vectors satisfying `eq9OrthoPairsB`, together with unitarity of twice each adjoint
branch Kraus operator and restoration of every operator with weight one quarter. -/
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

/-- The number of two-bit branch outcomes, defined as the cardinality of `Bool × Bool`. -/
def Clause1BranchCount : ℕ := Fintype.card (Bool × Bool)

/-- The common complex restoration weight `1 / 4`. -/
noncomputable def Clause1RestoreWeight : ℂ := 1 / 4

end Qatlib.Papers.MeasureOnly00.TeleportBound
