/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

/-!
# Statement of source-constrained fidelity-level optimality

`SourceFidelityLevelSubgoal` packages the existence and optimality statement for a water-filling
profile with a prescribed fidelity threshold. Its hypotheses specify normalized nonnegative
source and positive target profiles and tight, distinct bracket endpoints; its conclusion bounds
the squared mass of every feasible source-box competitor. This is the profile optimization
underlying quantum rejection sampling [OzolsRoettelerRoland2013].

## Main statements

* `SourceFidelityLevelSubgoal`: state existence of a fidelity level and its source-box mass
  bound.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.LevelFidelity

open scoped BigOperators

/-- The proposition that normalized source and target profiles with the specified tight
nondegenerate bracket possess a water level for each allowed fidelity threshold, whose
filled mass bounds every feasible source-box vector's squared norm. -/
def SourceFidelityLevelSubgoal : Prop :=
  ∀ (m : ℕ) (π σ : Fin m → ℚ) (γlo γhi : ℝ),
    (∀ i, 0 ≤ π i) → (∀ i, 0 < σ i) →
    (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
    γlo < γhi →
    (∀ i, 0 < π i → γlo * (σ i : ℝ) ≤ (π i : ℝ)) →
    (∃ i₀, 0 < π i₀ ∧ γlo * (σ i₀ : ℝ) = (π i₀ : ℝ)) →
    (∀ i, (π i : ℝ) ≤ γhi * (σ i : ℝ)) →
    (∃ i₁, 0 < π i₁ ∧ (π i₁ : ℝ) = γhi * (σ i₁ : ℝ)) →
    ∀ p : ℝ, waterPmin π σ ≤ p → p ≤ waterPmax π σ →
      ∃ gbar : ℝ, γlo ≤ gbar ∧ gbar ≤ γhi ∧
        levelDot π σ gbar ^ 2 = p * levelMass π σ gbar ∧
        ∀ v : Fin m → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ (π i : ℝ)) →
          p * (∑ i, v i ^ 2) ≤ (∑ i, (σ i : ℝ) * v i) ^ 2 →
          (∑ i, v i ^ 2) ≤ levelMass π σ gbar

end Qatlib.Concepts.Waterfill.LevelFidelity
