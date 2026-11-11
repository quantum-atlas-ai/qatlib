/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

set_option backward.isDefEq.respectTransparency false

/-!
# SourceDefinitions — Definitions 1–3 of the variable-time amplification

Low--Su, fixed arXiv:2410.18178v2,
PDF SHA-256 5bc33df5fbcd340bd3381e798bb80a436fdc6596027697440f882c15769de5a6.

The paper's Definition 1 (p.17, variable-time algorithm and amplification),
Definition 2 (p.18, variable-time nested amplitude amplification) and
Definition 3 (p.20, Tunable VTAA) are bundling definitions. The library keeps
their content in `clockLegal`, `stageLegal`, `nestedWord`, `aaWord` and
`tunable` of the frozen source paid model. This module packages exactly those
definitions into paper-facing structures and proves the defining interface
laws, so that the later claims can refer to a single paper-level object.

Boundary: the structures contain only the paper's data and the frozen legality
predicates; no cost or correctness claim is added here.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.QLSStatePrep24.Amplification

/-- Fixed arXiv:2410.18178v2, Definition 1 (p.17): a variable-time algorithm
consists of a clock family of orthogonal projections `P 0 = 0 ≤ … ≤ P m = 1`,
a failure flag `bad` commuting with every clock projection, stage unitaries
`U (j+1)` that fix the preceding clock projection `P j`, and a normalized
initial state `ω`. The legality predicates are the frozen `clockLegal` and
`stageLegal`. -/
structure VariableTimeAlgorithm (H : Type) [Fintype H] [DecidableEq H] (m : ℕ) where
  /-- Clock projections `Π_j`, `j = 0, …, m`. -/
  P : Fin (m+1) → Matrix H H ℂ
  /-- Failure-flag projection `Π_b`. -/
  bad : Matrix H H ℂ
  /-- Stage unitaries `A_j`, indexed so that `U (j+1)` is the `(j+1)`-th stage. -/
  U : ℕ → Matrix H H ℂ
  /-- Initial state `|ψ₀⟩`. -/
  omega : QState H
  /-- The clock family is ordered, begins at `0`, ends at `1`, and `bad` commutes. -/
  clock : clockLegal m P bad
  /-- Every stage is unitary and fixes the preceding clock projection. -/
  stage : stageLegal m P U
  /-- The initial state is normalized. -/
  normalized : Normalized omega

/-- Fixed arXiv:2410.18178v2, Definition 1 (p.17): the legality data of a
variable-time algorithm, unpacked from the frozen contract. -/
theorem def1_variable_time_algorithm_data {H : Type} [Fintype H] [DecidableEq H]
    {m : ℕ} (V : VariableTimeAlgorithm H m) :
    (∀ j, IsOrthogonalProjector (V.P j)) ∧ V.P 0 = 0 ∧ V.P ⟨m, by omega⟩ = 1 ∧
    IsOrthogonalProjector V.bad ∧ (∀ j, V.P j * V.bad = V.bad * V.P j) ∧
    (∀ j : Fin m, V.U (j.val+1) * V.P ⟨j.val, by omega⟩ = V.P ⟨j.val, by omega⟩) := by
  obtain ⟨P, bad, U, omega, hclock, hstage, hnorm⟩ := V
  exact ⟨hclock.1, hclock.2.1, hclock.2.2.1, hclock.2.2.2.2.1, hclock.2.2.2.2.2, hstage.2⟩

/-- Fixed arXiv:2410.18178v2, Definition 2 (p.18): variable-time nested
amplitude amplification is a clock/failure family together with an integer
round schedule, where each stage runs `2 r_j + 1` amplitude-amplification
rounds of the same success projection `potential (P (j+1)) bad`. The recursive
word is the frozen `nestedWord`. -/
structure NestedAmplification (H : Type) [Fintype H] [DecidableEq H] (m : ℕ) where
  /-- Clock family (extended to all natural indices by `extendClock` in the paper). -/
  P : ℕ → Matrix H H ℂ
  /-- Failure flag. -/
  bad : Matrix H H ℂ
  /-- Initial state. -/
  omega : QState H
  /-- Integer rounds `r_j` per stage. -/
  rounds : ℕ → ℕ

/-- Fixed arXiv:2410.18178v2, Definition 2 (p.18): the recursive word of
variable-time nested amplitude amplification, with the base stage `0` and the
amplification of stage `j+1` by the same success projection. -/
theorem def2_nested_word_recursion {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (A : NestedAmplification H m) :
    nestedWord A.P A.bad A.omega A.rounds 0 = stageWord 0 ∧
    ∀ j : ℕ,
      nestedWord A.P A.bad A.omega A.rounds (j+1) =
        aaWord (nestedWord A.P A.bad A.omega A.rounds j ++ stageWord (j+1))
          A.omega (potential (A.P (j+1)) A.bad) (A.rounds (j+1)) :=
  ⟨rfl, fun _ => rfl⟩

/-- Fixed arXiv:2410.18178v2, Definition 3 (p.20): Tunable VTAA is a
variable-time algorithm together with a threshold schedule `α` satisfying
`α 0 = 1`, `0 ≤ α (j+1)`, the minimality ceiling
`√α_{j+1}/3 ≤ (2 r_{j+1}+1) a_j`, and strict minimality for smaller round
counts, where `a_j` is the known preceding pre-amplification amplitude. -/
structure TunableSchedule (H : Type) [Fintype H] [DecidableEq H] (m : ℕ) where
  /-- Clock family. -/
  P : ℕ → Matrix H H ℂ
  /-- Failure flag. -/
  bad : Matrix H H ℂ
  /-- Stage unitaries. -/
  U : ℕ → Matrix H H ℂ
  /-- Initial state. -/
  omega : QState H
  /-- Threshold schedule `α`. -/
  alpha : ℕ → ℝ
  /-- Round schedule. -/
  rounds : ℕ → ℕ
  /-- The frozen `tunable` predicate. -/
  isTunable : tunable m P bad U omega alpha rounds

/-- Fixed arXiv:2410.18178v2, Definition 3 (p.20): the defining schedule
inequalities of a Tunable VTAA. -/
theorem def3_tunable_schedule_data {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (S : TunableSchedule H m) :
    S.alpha 0 = 1 ∧ ∀ j < m,
      0 ≤ S.alpha (j+1) ∧
      Real.sqrt (S.alpha (j+1))/3 ≤
        (2*S.rounds (j+1)+1)*preAmplitude S.P S.bad S.omega S.U S.rounds j ∧
      ∀ s < S.rounds (j+1),
        (2*s+1)*preAmplitude S.P S.bad S.omega S.U S.rounds j <
          Real.sqrt (S.alpha (j+1))/3 := by
  obtain ⟨P, bad, U, omega, alpha, rounds, htun⟩ := S
  exact htun

end Qatlib.Papers.QLSStatePrep24.Amplification
