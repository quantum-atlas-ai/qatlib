/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-!
# Phase-readout stability contract

Packages a bound on total variation between two phase-kernel label laws with phases in `[0, π /
2]`. This proposition is a phase-level component of the stability argument for Lemma 18 of
[Montanaro2015].

## Main statements

* `MontanaroLemma18PhaseTVSubgoal` specifies the bound in terms of the square root of `|sin² ω₁
  - sin² ω₂|` and a grid size at least one.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition requiring phase-label total variation to be at most `π² * M / (2 * sqrt 3) *
sqrt |sin² ω₁ - sin² ω₂|`, for phases in `[0, π / 2]` and `M ≥ 1`. -/
def MontanaroLemma18PhaseTVSubgoal : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ ω₁ ω₂ : ℝ, 0 ≤ ω₁ → ω₁ ≤ Real.pi / 2 → 0 ≤ ω₂ →
    ω₂ ≤ Real.pi / 2 →
    (1 / 2 : ℝ) * ∑ z : Fin M,
        |‖qpeKernel M ω₁ z‖ ^ 2 - ‖qpeKernel M ω₂ z‖ ^ 2|
      ≤ (Real.pi ^ 2 / (2 * Real.sqrt 3)) * (M : ℝ) *
        Real.sqrt |(Real.sin ω₁) ^ 2 - (Real.sin ω₂) ^ 2|

end Qatlib.Concepts.EstimatorLaws.TvStability
