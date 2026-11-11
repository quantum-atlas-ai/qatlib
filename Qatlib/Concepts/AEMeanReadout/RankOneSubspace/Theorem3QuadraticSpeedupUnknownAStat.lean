/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget

/-!
# Specification of search with unknown success mass

`Theorem3QuadraticSpeedupUnknownA` specifies geometric search schedules for prepared marked mass
`sin² θ` with `0 < θ ≤ π/4`. It requires an arbitrarily small failure bound, a uniform bound on
expected preparation calls, and sound successful outputs. For background, see
[BrassardHoyerTapp1998Counting].

## Main statements

* `Theorem3QuadraticSpeedupUnknownA`: The proposition that a unitary preparation with marked
  mass `sin² θ` and `0 < θ ≤ π/4` has geometric search schedules achieving every positive
  failure tolerance, expected preparation count at most `150 * sqrt 2 / sin θ`, and only marked
  successful outputs.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib
open scoped ENNReal

/-- The proposition that a unitary preparation with marked mass `sin² θ` and `0 < θ ≤ π/4` has
geometric search schedules achieving every positive failure tolerance, expected preparation
count at most `150 * sqrt 2 / sin θ`, and only marked successful outputs. -/
def Theorem3QuadraticSpeedupUnknownA : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j₀ : I)
    (S : Finset I),
    (hA : A ∈ Matrix.unitaryGroup I ℂ) →
    ∀ (θ : ℝ), (hθ0 : 0 < θ) → (hθ4 : θ ≤ Real.pi / 4) →
      (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) →
      ∀ (ε : ℝ), (hε : 0 < ε) →
        ∃ (M T : ℕ),
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
              (geometricSearchSchedule M T)) (fun tr => tr.result = none) ≤
            ENNReal.ofReal ε ∧
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
              (geometricSearchSchedule M T)) (fun tr => (tr.prepareCalls : ℝ≥0∞)) ≤
            ENNReal.ofReal (150 * Real.sqrt 2 / Real.sin θ) ∧
          ∀ tr ∈ (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
              (geometricSearchSchedule M T)).support,
            ∀ y, tr.result = some y → y ∈ S

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
