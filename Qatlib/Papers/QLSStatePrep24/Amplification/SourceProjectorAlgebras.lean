/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.StoppedStageTransportLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.AmplifiedSuffixRaysLows

set_option backward.isDefEq.respectTransparency false

/-!
# SourceProjectorAlgebras — projector chain of the variable-time amplification

Low--Su, "Quantum linear system algorithm with optimal queries to initial state
preparation", fixed arXiv:2410.18178v2,
PDF SHA-256 5bc33df5fbcd340bd3381e798bb80a436fdc6596027697440f882c15769de5a6.

This module connects the paper's projection lemmas -- Lemma 10 (p.41),
Proposition 11 (p.42), Proposition 12 (p.42), Lemma 13 (p.43),
Proposition 14 (p.44), Proposition 15 (p.45) -- to the library statements
`Clause2ProjectorOrder`, `Clause3ClockFlagResolutions`, `Clause4StoppedStageTransport` and
`Clause6AmplifiedSuffixRays`. These statements are proved by the corresponding
library theorems.

Scope note: statements use the paper's abstraction level (finite Hilbert
space, orthogonal projections, unitaries fixing clock projections). Cost
bounds and compilation are outside the scope of this file.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.QLSStatePrep24.Amplification

/-- Fixed arXiv:2410.18178v2, Lemma 10 (p.41): for orthogonal projections
`P Q` (paper `Π₁ = P`, `Π₂ = Q`), the inclusion of images, the two products
`QP = P` and `PQ = P`, the projector character of `Q - P`, the compression
identity `PQP = P`, positive semidefiniteness of `Q - P`, and pointwise norm
domination are all equivalent. Bridge to
`Clause2ProjectorOrder_answer`. -/
theorem lemma10_partially_ordered_projections {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    ((∀ ψ : QState H, P *ᵥ ψ = ψ → Q *ᵥ ψ = ψ) ↔ Q * P = P) ∧
    ((∀ ψ : QState H, Q *ᵥ ψ = 0 → P *ᵥ ψ = 0) ↔ Q * P = P) ∧
    (Q * P = P ↔ P * Q = P) ∧
    (Q * P = P ↔ IsOrthogonalProjector (Q - P)) ∧
    (Q * P = P ↔ P * Q * P = P) ∧
    (Q * P = P ↔ (Q - P).PosSemidef) ∧
    (Q * P = P ↔ ∀ ψ : QState H, normVec (P *ᵥ ψ) ≤ normVec (Q *ᵥ ψ)) :=
  Clause2ProjectorOrder_answer H P Q hP hQ

/-- Fixed arXiv:2410.18178v2, Proposition 11 (p.42): a legal clock family
`P` with failure flag `bad` is totally ordered, so for `j ≤ k` the products
collapse (`P k * P j = P j` and `P j * P k = P j`), the complements satisfy the
dual identities, and `P k - P j` is again an orthogonal projection. -/
theorem prop11_clock_flag_order {H : Type} [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ) (h : clockLegal m P bad) :
    ∀ j k : Fin (m+1), j.val ≤ k.val →
      P k * P j = P j ∧ P j * P k = P j ∧
      (1 - P j) * (1 - P k) = 1 - P k ∧ (1 - P k) * (1 - P j) = 1 - P k ∧
      IsOrthogonalProjector (P k - P j) := by
  intro j k hjk
  have h' := (Clause3ClockFlagResolutions_answer H m P bad h).1 j k hjk
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1⟩

/-- Fixed arXiv:2410.18178v2, Proposition 12 (p.42): the clock differences
`P (j+1) - P j` resolve the identity, each is an orthogonal projection that
commutes with the failure flag (and its flagged/unflagged parts are projections
as well), and distinct differences are orthogonal. -/
theorem prop12_clock_flag_resolution_of_identity {H : Type} [Fintype H] [DecidableEq H]
    (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (h : clockLegal m P bad) :
    (∑ j : Fin m, (P ⟨j.val+1, by omega⟩ - P ⟨j.val, by omega⟩)) = 1 ∧
    (∀ j : Fin m,
      IsOrthogonalProjector (P ⟨j.val+1, by omega⟩ - P ⟨j.val, by omega⟩) ∧
      IsOrthogonalProjector ((P ⟨j.val+1, by omega⟩ - P ⟨j.val, by omega⟩) * bad)) ∧
    (∀ j k : Fin m, j ≠ k →
      (P ⟨j.val+1, by omega⟩ - P ⟨j.val, by omega⟩) *
        (P ⟨k.val+1, by omega⟩ - P ⟨k.val, by omega⟩) = 0) := by
  have h' := Clause3ClockFlagResolutions_answer H m P bad h
  refine ⟨h'.2.1, ?_, h'.2.2.2.1⟩
  intro j
  exact ⟨(h'.2.2.1 j).1, (h'.2.2.1 j).2.2.1⟩

/-- Fixed arXiv:2410.18178v2, Lemma 13 (p.43): for a unitary `U` and an
orthogonal projection `P`, the conditions `U P = P`, `P U = P`,
`P U P = P` and `U = P + (1 - P) U (1 - P)` are all equivalent. -/
theorem lemma13_controlled_unitaries {H : Type} [Fintype H] [DecidableEq H]
    (P U : Matrix H H ℂ) (hP : IsOrthogonalProjector P)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    (U * P = P ↔ P * U = P) ∧
    (U * P = P ↔ P * U * P = P) ∧
    (U * P = P ↔ U = P + (1 - P) * U * (1 - P)) :=
  (Clause4StoppedStageTransport_answer).1 H P U hP hU

/-- Fixed arXiv:2410.18178v2, Proposition 14 (p.44): stage unitaries
`U (j+1)` that fix the preceding clock projection `P j` commute with every
earlier clock projection and its failure-flagged potential, and stopped suffix
evolution preserves the potential-weighted norm. -/
theorem prop14_stopped_stage_transport {H : Type} [Fintype H] [DecidableEq H]
    (m : ℕ) (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (hclock : clockLegal m P bad) (hstage : stageLegal m P U) :
    (∀ j k : Fin (m+1), j.val < k.val →
      U k.val * P j = P j ∧ P j * U k.val = P j ∧
      U k.val * potential (P j) bad = potential (P j) bad * U k.val) ∧
    (∀ (j k : Fin (m+1)) (ψ : QState H), j.val ≤ k.val →
      normVec (potential (P j) bad *ᵥ suffixState U j.val k.val ψ) =
      normVec (potential (P j) bad *ᵥ ψ)) :=
  let h' := (Clause4StoppedStageTransport_answer).2 H m P bad U hclock hstage
  ⟨h'.1, h'.2.1⟩

/-- Fixed arXiv:2410.18178v2, Proposition 15 (p.45): amplified suffix rays are
independent of the starting stage, and their potential-weighted ratios agree
across suffixes. Bridge to `Clause6AmplifiedSuffixRays_answer`. -/
theorem prop15_amplified_suffix_rays : Clause6AmplifiedSuffixRays :=
  Clause6AmplifiedSuffixRays_answer

end Qatlib.Papers.QLSStatePrep24.Amplification
