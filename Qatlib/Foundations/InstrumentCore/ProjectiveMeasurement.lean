/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.InstrumentCore.Measurement.Basic
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib
open Qatlib

namespace Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev IsOrthogonalProjector (P : Matrix I I ℂ) : Prop := IsStarProjection P

noncomputable def ConditionalState (ψ : QState I) : Option (QState I) :=
  if 0 < MeasureProb ψ Finset.univ then some (PostMeasure ψ Finset.univ) else none

theorem normalized_of_conditionalState_eq_some {ψ φ : QState I}
    (h : ConditionalState ψ = some φ) : Normalized φ := by
  unfold ConditionalState at h
  split_ifs at h with hp
  · cases Option.some.inj h
    exact normalized_postMeasure hp

@[simp] theorem conditionalState_zero : ConditionalState (0 : QState I) = none := by
  simp [ConditionalState, MeasureProb, BornProb]

theorem conditionalState_collapse {ψ : QState I} {S : Finset I}
    (h : 0 < MeasureProb ψ S) : ConditionalState (Collapse ψ S) = some (PostMeasure ψ S) := by
  have hm : MeasureProb (Collapse ψ S) Finset.univ = MeasureProb ψ S := by
    simpa [MeasureProb, BornProb] using sum_normSq_collapse ψ S
  unfold ConditionalState
  rw [hm, if_pos h]
  congr 1
  funext i
  simp [PostMeasure, hm, collapse_apply]

noncomputable def ProjectiveBranch (P : Matrix I I ℂ) (outcome : Bool)
    (ψ : QState I) : QState I :=
  ApplyGate (if outcome then P else 1 - P) ψ

noncomputable def ProjectiveBranchMass (P : Matrix I I ℂ) (outcome : Bool)
    (ψ : QState I) : ℝ :=
  MeasureProb (ProjectiveBranch P outcome ψ) Finset.univ

noncomputable def ProjectiveConditionalState (P : Matrix I I ℂ) (outcome : Bool)
    (ψ : QState I) : Option (QState I) :=
  ConditionalState (ProjectiveBranch P outcome ψ)

noncomputable def ProjectiveHistoryState
    (history : List (Matrix I I ℂ × Bool)) (ψ : QState I) : QState I :=
  history.foldl (fun state step => ProjectiveBranch step.1 step.2 state) ψ

noncomputable def ProjectiveHistoryMass
    (history : List (Matrix I I ℂ × Bool)) (ψ : QState I) : ℝ :=
  MeasureProb (ProjectiveHistoryState history ψ) Finset.univ

theorem projectiveBranchMass_nonneg (P : Matrix I I ℂ) (o : Bool) (ψ : QState I) :
    0 ≤ ProjectiveBranchMass P o ψ := measureProb_nonneg _ _

@[simp] theorem projectiveBranch_projector (S : Finset I) (ψ : QState I) :
    ProjectiveBranch (Projector S) true ψ = Collapse ψ S := rfl

theorem projector_isOrthogonalProjector (S : Finset I) :
    IsOrthogonalProjector (Projector S) :=
  ⟨projector_mul_self S, projector_conjTranspose S⟩

end Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
