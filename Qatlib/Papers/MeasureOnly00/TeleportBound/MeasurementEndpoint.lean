/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementPatterns

/-!
# Teleportation endpoint identities

`teleport_endpoint_exists` supplies a unitary correction for each two-bit branch under
`eq9OrthoPairsB`, with corrected action equal to one quarter of any input operator. The module
also records the four-branch weight sum and the convex pure state decomposition of density
operators. The measurement-only computation context is [RaussendorfBriegel2000].

## Main statements

* `teleport_endpoint_exists`: unitary corrections and restoration on arbitrary operators.
* `teleport_branch_weights_sum`: the four restoration weights sum to one.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

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

/-- For resource vectors satisfying `eq9OrthoPairsB`, twice the adjoint branch Kraus operator is
unitary, and the corresponding corrected branch sends every operator `ρ` to `(1 / 4) • ρ`. -/
theorem teleport_endpoint_exists :
    ∀ (u v p q : QState Bool), eq9OrthoPairsB u v p q → ∀ o : Bool × Bool,
      (((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ∀ ρ : Operator 2,
        ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o) * ρ *
          ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o)ᴴ
            = (1 / 4 : ℂ) • ρ :=
  clause1_endpoint_exists

/-- The teleportation branch count is four. -/
theorem teleport_branch_count : Clause1BranchCount = 4 :=
  clause1_branchCount

/-- The restoration weight of each teleportation branch is the complex scalar `1 / 4`. -/
theorem teleport_restore_weight : Clause1RestoreWeight = (1 / 4 : ℂ) :=
  clause1_restoreWeight

/-- The product of the branch count and the common restoration weight is one. -/
theorem teleport_branch_weights_sum :
    Clause1BranchCount * Clause1RestoreWeight = (1 : ℂ) :=
  clause1_branchWeights_sum

/-- Every density operator is a convex combination of `D` normalized pure state outer products,
with nonnegative real weights summing to one. -/
theorem teleport_mixed_pure_equivalence {D : ℕ} {ρ : Operator D}
    (hρ : IsDensityOperator ρ) :
    ∃ (w : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ k, 0 ≤ w k) ∧ (∀ k, Normalized (ψ k)) ∧ (∑ k, w k = 1) ∧
        ρ = ∑ k, (w k : ℂ) • outerProduct (ψ k) :=
  clause2_mixed_pure_equivalence hρ

end Qatlib.Papers.MeasureOnly00.TeleportBound
