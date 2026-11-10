/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

def MontanaroLemma18PhaseTVSubgoal : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ ω₁ ω₂ : ℝ, 0 ≤ ω₁ → ω₁ ≤ Real.pi / 2 → 0 ≤ ω₂ →
    ω₂ ≤ Real.pi / 2 →
    (1 / 2 : ℝ) * ∑ z : Fin M,
        |‖qpeKernel M ω₁ z‖ ^ 2 - ‖qpeKernel M ω₂ z‖ ^ 2|
      ≤ (Real.pi ^ 2 / (2 * Real.sqrt 3)) * (M : ℝ) *
        Real.sqrt |(Real.sin ω₁) ^ 2 - (Real.sin ω₂) ^ 2|

end Qatlib.Concepts.EstimatorLaws.TvStability
