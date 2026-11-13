/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwEigenBranches

/-!
# Alternating measurements and agreement records

`alternatingState` applies selected outcomes of two alternating projectors, and
`agreementRecord` records whether consecutive outcomes coincide. The inverse encoding
`outcomeRecord` connects physical outcomes with the branch recursion, giving an explicit mass
formula on compressed-projector eigenvectors.

The mathematical background is developed in [MarriottWatrous2005].

## Main statements

* `agreement_outcome`: shows that decoding an agreement record recovers it under re-encoding.
* `alternating_eq_branch`: identifies alternating outcomes with agreement-indexed branches.
* `actual_record_mass`: computes alternating record mass for a clean eigenvector.
* `two_reflections_unitary`: proves unitarity of the product of the corresponding reflections.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators
variable {H : Type} [Fintype H] [DecidableEq H]

/-- Selects `P` for a true measurement outcome and `1 - P` for a false outcome. -/
noncomputable def selected (P : Matrix H H ℂ) (b : Bool) := if b then P else 1 - P

/-- The unnormalized state obtained by applying the selected outcomes while alternating between
`P` and `Q`. -/
noncomputable def alternatingState (P Q : Matrix H H ℂ) (_previous : Bool) :
    List Bool → QState H → QState H
  | [], ψ => ψ
  | b :: rest, ψ => alternatingState Q P b rest (selected P b *ᵥ ψ)

/-- Encodes an outcome list by whether each outcome equals the preceding outcome, starting from
`previous`. -/
def agreementRecord (previous : Bool) : List Bool → List Bool
  | [] => []
  | b :: rest => (b == previous) :: agreementRecord b rest

/-- Reconstructs outcomes from agreement bits, starting from `previous` and flipping it whenever
an agreement bit is false. -/
def outcomeRecord (previous : Bool) : List Bool → List Bool
  | [] => []
  | b :: rest =>
    let next := if b then previous else !previous
    next :: outcomeRecord next rest

/-- Encoding the outcomes reconstructed from an agreement record returns the original agreement
record. -/
theorem agreement_outcome (previous : Bool) (z : List Bool) :
    agreementRecord previous (outcomeRecord previous z) = z := by
  induction z generalizing previous with
  | nil => rfl
  | cons b zs ih => cases b <;> cases previous <;> simp [outcomeRecord, agreementRecord, ih]

/-- Reconstructing outcomes from their agreement record returns the original outcome list. -/
theorem outcome_agreement (previous : Bool) (ys : List Bool) :
    outcomeRecord previous (agreementRecord previous ys) = ys := by
  induction ys generalizing previous with
  | nil => rfl
  | cons b ys ih => cases b <;> cases previous <;> simp [outcomeRecord, agreementRecord, ih]

/-- The agreement encoding preserves the length of an outcome list. -/
@[simp] theorem agreement_length (previous : Bool) (ys : List Bool) :
    (agreementRecord previous ys).length = ys.length := by
  induction ys generalizing previous with
  | nil => rfl
  | cons b ys ih => simp [agreementRecord, ih]

/-- Alternating measurement outcomes give the same state as the branch recursion indexed by
their agreement record and initialized with the selected previous-outcome projectors. -/
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

/-- For a vector fixed by `Q` with compressed eigenvalue `p`, alternating record mass equals its
initial mass times the weight of the corresponding agreement record. -/
theorem actual_record_mass (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (ψ : QState H) (p : ℝ) (hfix : Q *ᵥ ψ = ψ)
    (heig : Q *ᵥ (P *ᵥ ψ) = (p : ℂ) • ψ) (ys : List Bool) :
    MeasureProb (alternatingState P Q true ys ψ) Finset.univ =
      recordWeight p (agreementRecord true ys) * MeasureProb ψ Finset.univ := by
  rw [alternating_eq_branch]
  exact record_mass Q P hQ hP ψ p hfix heig _

/-- The product of the reflections associated with two orthogonal projectors is unitary. -/
theorem two_reflections_unitary (P Q : Matrix H H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    ReflectionAbout Q * ReflectionAbout P ∈ unitaryGroup H ℂ :=
  (unitaryGroup H ℂ).mul_mem (reflectionAbout_unitary hQ) (reflectionAbout_unitary hP)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
