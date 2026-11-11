/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic

/-!
# Binary projective measurement branches

`ProjectiveBranch` applies either `P` or `1 - P` according to a Boolean outcome, and
`ProjectiveBranchMass` records its total Born mass. `ConditionalState` returns a normalized
state only when that mass is positive.

`ProjectiveHistoryState` composes branches in list order, with `ProjectiveHistoryMass` recording
the final unnormalized mass. Orthogonal projectors are represented by `IsOrthogonalProjector`;
see [NielsenChuang2010] for projective measurement.

## Main statements

* `ConditionalState`: Optional normalization of a state of positive mass.
* `ProjectiveBranch`: Unnormalized branch for a Boolean outcome.
* `ProjectiveHistoryState`: Sequential application of specified outcomes.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib
open Qatlib

namespace Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The predicate that `P` is a self-adjoint idempotent matrix. -/
abbrev IsOrthogonalProjector (P : Matrix I I ℂ) : Prop := IsStarProjection P

/-- Returns the normalization of `ψ` when its total Born mass is positive, and `none` otherwise. -/
noncomputable def ConditionalState (ψ : QState I) : Option (QState I) :=
  if 0 < MeasureProb ψ Finset.univ then some (PostMeasure ψ Finset.univ) else none

/-- Every state returned by `ConditionalState` is normalized. -/
theorem normalized_of_conditionalState_eq_some {ψ φ : QState I}
    (h : ConditionalState ψ = some φ) : Normalized φ := by
  unfold ConditionalState at h
  split_ifs at h with hp
  · cases Option.some.inj h
    exact normalized_postMeasure hp

/-- The zero state has no conditional normalized state. -/
@[simp] theorem conditionalState_zero : ConditionalState (0 : QState I) = none := by
  simp [ConditionalState, MeasureProb, BornProb]

/-- Normalizing a coordinate collapse of positive mass returns the corresponding `PostMeasure`
state. -/
theorem conditionalState_collapse {ψ : QState I} {S : Finset I}
    (h : 0 < MeasureProb ψ S) : ConditionalState (Collapse ψ S) = some (PostMeasure ψ S) := by
  have hm : MeasureProb (Collapse ψ S) Finset.univ = MeasureProb ψ S := by
    simpa [MeasureProb, BornProb] using sum_normSq_collapse ψ S
  unfold ConditionalState
  rw [hm, if_pos h]
  congr 1
  funext i
  simp [PostMeasure, hm, collapse_apply]

/-- Applies `P` for outcome `true` and `1 - P` for outcome `false`, without normalization. -/
noncomputable def ProjectiveBranch (P : Matrix I I ℂ) (outcome : Bool)
    (ψ : QState I) : QState I :=
  ApplyGate (if outcome then P else 1 - P) ψ

/-- The total Born mass of the selected unnormalized projective branch. -/
noncomputable def ProjectiveBranchMass (P : Matrix I I ℂ) (outcome : Bool)
    (ψ : QState I) : ℝ :=
  MeasureProb (ProjectiveBranch P outcome ψ) Finset.univ

/-- The optional normalized state of the selected projective branch. -/
noncomputable def ProjectiveConditionalState (P : Matrix I I ℂ) (outcome : Bool)
    (ψ : QState I) : Option (QState I) :=
  ConditionalState (ProjectiveBranch P outcome ψ)

/-- The unnormalized state obtained by applying the listed matrix-outcome branches from left to
right. -/
noncomputable def ProjectiveHistoryState
    (history : List (Matrix I I ℂ × Bool)) (ψ : QState I) : QState I :=
  history.foldl (fun state step => ProjectiveBranch step.1 step.2 state) ψ

/-- The total Born mass remaining after the specified history of projective branches. -/
noncomputable def ProjectiveHistoryMass
    (history : List (Matrix I I ℂ × Bool)) (ψ : QState I) : ℝ :=
  MeasureProb (ProjectiveHistoryState history ψ) Finset.univ

/-- Every projective branch mass is nonnegative. -/
theorem projectiveBranchMass_nonneg (P : Matrix I I ℂ) (o : Bool) (ψ : QState I) :
    0 ≤ ProjectiveBranchMass P o ψ := measureProb_nonneg _ _

/-- The `true` branch of a coordinate projector is the corresponding coordinate collapse. -/
@[simp] theorem projectiveBranch_projector (S : Finset I) (ψ : QState I) :
    ProjectiveBranch (Projector S) true ψ = Collapse ψ S := rfl

/-- Every finite coordinate projector is an orthogonal projector. -/
theorem projector_isOrthogonalProjector (S : Finset I) :
    IsOrthogonalProjector (Projector S) :=
  ⟨projector_mul_self S, projector_conjTranspose S⟩

end Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
