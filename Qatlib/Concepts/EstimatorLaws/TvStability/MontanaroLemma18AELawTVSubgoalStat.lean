/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

def MontanaroLemma18AELawTVSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M),
    ∀ (A₁ A₂ : Matrix I I ℂ) (j₁ j₂ : I) (S₁ S₂ : Finset I),
    ∀ (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ),
    ∀ (μ₁ μ₂ : ℝ), MeasureProb (preparedAAState A₁ j₁) S₁ = μ₁ →
      MeasureProb (preparedAAState A₂ j₂) S₂ = μ₂ →
      (1 / 2 : ℝ) * ∑ z : Fin M,
          |(aeLaw M A₁ j₁ S₁ hA₁ hM).prob z
            - (aeLaw M A₂ j₂ S₂ hA₂ hM).prob z|
        ≤ (Real.pi ^ 2 / (2 * Real.sqrt 3)) * (M : ℝ) * Real.sqrt |μ₁ - μ₂|

end Qatlib.Concepts.EstimatorLaws.TvStability
