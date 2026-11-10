/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChiSqOverlapSubgoalStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityStat

open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

namespace Qatlib.Concepts.EstimatorLaws.TvStability

noncomputable def chiSqGibbsSum {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ : ℝ) : ℝ :=
  (∑ x : Ω, (Real.exp (-(β₂ * (H x : ℝ)))) ^ 2 / Real.exp (-(β₁ * (H x : ℝ))))
    / partitionFn H β₂ ^ 2

noncomputable def gibbsOverlap {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ : ℝ) : ℝ :=
  (∑ x : Ω, Real.exp (-((β₁ + β₂) / 2 * (H x : ℝ))))
    / Real.sqrt (partitionFn H β₁ * partitionFn H β₂)

def MontanaroChiSqScheduleOverlapSubgoal : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ B : ℝ), β₁ ≤ β₂ →
    0 < partitionFn H β₁ → 0 < partitionFn H β₂ → 0 < B →
    partitionFn H β₁ * partitionFn H (2 * β₂ - β₁) ≤ B * partitionFn H β₂ ^ 2 →
    chiSqGibbsSum H β₁ β₂
      = partitionFn H β₁ * partitionFn H (2 * β₂ - β₁) / partitionFn H β₂ ^ 2 ∧
    1 / B ≤ gibbsOverlap H β₁ β₂ ^ 2

end Qatlib.Concepts.EstimatorLaws.TvStability

set_option autoImplicit false
namespace Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
noncomputable section

def chiSqGibbsSumCorrected {Ω : Type} [Fintype Ω] (H : Ω→ℕ) (β₁ β₂ : ℝ) : ℝ :=
  partitionFn H β₁*chiSqGibbsSum H β₁ β₂
end
end Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
