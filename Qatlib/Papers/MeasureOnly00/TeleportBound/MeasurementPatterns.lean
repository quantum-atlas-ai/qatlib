/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MeasureOnly00.TeleportBound.MeasurementPatternsDefs
import Qatlib.Concepts.QuditTeleport.ResourceIff.Eq9ResourceTeleportationTele
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional

/-!
# Measurement pattern endpoints and branch weights

`clause1_endpoint_exists` proves branch correction and restoration identities for resources
satisfying `eq9OrthoPairsB`. `endpointOfOrtho` packages these identities into `Clause1Endpoint`,
while the remaining results compute branch weights and decompose mixed states into pure states.
The measurement-only computation context is [RaussendorfBriegel2000].

## Main statements

* `endpointOfOrtho`: constructs an endpoint record from the orthogonality data.
* `clause1_branchWeights_sum`: total restoration weight is one.
* `clause2_mixed_pure_equivalence`: convex pure state decomposition.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.ResourceIff

namespace Qatlib.Papers.MeasureOnly00.TeleportBound

open Matrix

/-- For resource vectors satisfying `eq9OrthoPairsB`, twice the adjoint of each branch Kraus
operator is a unitary correction whose corrected branch sends any operator to one quarter of
itself. -/
theorem clause1_endpoint_exists :
    ∀ (u v p q : QState Bool), eq9OrthoPairsB u v p q → ∀ o : Bool × Bool,
      (((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      ∀ ρ : Operator 2,
        ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o) * ρ *
          ((2 : ℂ) • (eq9BranchKraus u v p q o)ᴴ * eq9BranchKraus u v p q o)ᴴ
            = (1 / 4 : ℂ) • ρ := by
  intro u v p q h o
  have hcontract : Eq9ResourceTeleportation := eq9ResourceTeleportation
  exact hcontract u v p q h o

/-- The endpoint pattern has four two-bit branches. -/
theorem clause1_branchCount : Clause1BranchCount = 4 := by
  simp [Clause1BranchCount]

/-- Constructs a `Clause1Endpoint` from four vectors satisfying `eq9OrthoPairsB`, using the
branch correction and restoration identities. -/
noncomputable def endpointOfOrtho (u v p q : QState Bool)
    (h : eq9OrthoPairsB u v p q) : Clause1Endpoint where
  u := u
  v := v
  p := p
  q := q
  ortho := h
  correctionUnitary o := (clause1_endpoint_exists u v p q h o).1
  restores o := (clause1_endpoint_exists u v p q h o).2

/-- The common branch restoration weight is the complex scalar `1 / 4`. -/
theorem clause1_restoreWeight : Clause1RestoreWeight = (1 / 4 : ℂ) := by
  rfl

/-- The branch count multiplied by the common restoration weight equals one. -/
theorem clause1_branchWeights_sum :
    Clause1BranchCount * Clause1RestoreWeight = (1 : ℂ) := by
  simp [Clause1BranchCount, Clause1RestoreWeight]

/-- Every density operator is a convex combination of `D` normalized pure state outer products,
with nonnegative real weights summing to one. -/
theorem clause2_mixed_pure_equivalence {D : ℕ} {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    ∃ (w : Fin D → ℝ) (ψ : Fin D → QState (Fin D)),
      (∀ k, 0 ≤ w k) ∧ (∀ k, Normalized (ψ k)) ∧ (∑ k, w k = 1) ∧
        ρ = ∑ k, (w k : ℂ) • outerProduct (ψ k) :=
  density_pure_decomposition ρ hρ

end Qatlib.Papers.MeasureOnly00.TeleportBound
