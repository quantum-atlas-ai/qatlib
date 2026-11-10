/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwEigenBranches
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators
variable {H : Type} [Fintype H] [DecidableEq H]

noncomputable def selected (P : Matrix H H ℂ) (b : Bool) := if b then P else 1 - P

noncomputable def alternatingState (P Q : Matrix H H ℂ) (_previous : Bool) :
    List Bool → QState H → QState H
  | [], ψ => ψ
  | b :: rest, ψ => alternatingState Q P b rest (selected P b *ᵥ ψ)

def agreementRecord (previous : Bool) : List Bool → List Bool
  | [] => []
  | b :: rest => (b == previous) :: agreementRecord b rest

def outcomeRecord (previous : Bool) : List Bool → List Bool
  | [] => []
  | b :: rest =>
    let next := if b then previous else !previous
    next :: outcomeRecord next rest

theorem agreement_outcome (previous : Bool) (z : List Bool) :
    agreementRecord previous (outcomeRecord previous z) = z := by
  induction z generalizing previous with
  | nil => rfl
  | cons b zs ih => cases b <;> cases previous <;> simp [outcomeRecord, agreementRecord, ih]

theorem outcome_agreement (previous : Bool) (ys : List Bool) :
    outcomeRecord previous (agreementRecord previous ys) = ys := by
  induction ys generalizing previous with
  | nil => rfl
  | cons b ys ih => cases b <;> cases previous <;> simp [outcomeRecord, agreementRecord, ih]

@[simp] theorem agreement_length (previous : Bool) (ys : List Bool) :
    (agreementRecord previous ys).length = ys.length := by
  induction ys generalizing previous with
  | nil => rfl
  | cons b ys ih => simp [agreementRecord, ih]

theorem alternating_eq_branch (P Q : Matrix H H ℂ) (previous : Bool)
    (ys : List Bool) (ψ : QState H) :
    alternatingState P Q previous ys ψ =
      branchState (selected Q previous) (selected P previous)
        (agreementRecord previous ys) ψ := by
  induction ys generalizing P Q previous ψ with
  | nil => rfl
  | cons b ys ih =>
    cases b <;> cases previous <;>
      simp [alternatingState, agreementRecord, selected, branchState, ih]

theorem actual_record_mass (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hfix : Q *ᵥ ψ = ψ)
    (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ) (ys : List Bool) :
    MeasureProb (alternatingState P Q true ys ψ) Finset.univ =
      recordWeight p (agreementRecord true ys) * MeasureProb ψ Finset.univ := by
  rw [alternating_eq_branch]
  exact record_mass Q P hQ hP ψ p hfix heig _

theorem two_reflections_unitary (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    ReflectionAbout Q * ReflectionAbout P ∈ unitaryGroup H ℂ :=
  (unitaryGroup H ℂ).mul_mem (reflectionAbout_unitary hQ) (reflectionAbout_unitary hP)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
