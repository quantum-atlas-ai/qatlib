/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementPatterns
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Papers.MeasureOnly00.TeleportBound

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix Qatlib

theorem teleport_endpoint_exists :
    ∀ (u v p q : QState Bool), eq9OrthoPairsB u v p q → ∀ o : Bool × Bool,
      (((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ∀ ρ : Operator 2,
        ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o) * ρ *
          ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o)ᴴ
            = (1 / 4 : ℂ) • ρ :=
  clause1_endpoint_exists

theorem teleport_branch_count : Clause1BranchCount = 4 :=
  clause1_branchCount

theorem teleport_restore_weight : Clause1RestoreWeight = (1 / 4 : ℂ) :=
  clause1_restoreWeight

theorem teleport_branch_weights_sum :
    Clause1BranchCount * Clause1RestoreWeight = (1 : ℂ) :=
  clause1_branchWeights_sum

theorem teleport_mixed_pure_equivalence {D : ℕ} {ρ : Operator D}
    (hρ : IsDensityOperator ρ) :
    ∃ (w : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ k, 0 ≤ w k) ∧ (∀ k, Normalized (ψ k)) ∧ (∑ k, w k = 1) ∧
        ρ = ∑ k, (w k : ℂ) • outerProduct (ψ k) :=
  clause2_mixed_pure_equivalence hρ

end Qatlib.Papers.MeasureOnly00.TeleportBound
