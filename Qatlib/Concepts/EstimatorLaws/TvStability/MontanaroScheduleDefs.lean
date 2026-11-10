/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

noncomputable def partitionFn {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β : ℝ) : ℝ :=
  ∑ x : Ω, Real.exp (-(β * (H x : ℝ)))
end Qatlib.Concepts.EstimatorLaws.TvStability

namespace Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

noncomputable def chiSqDist {X : Type} [Fintype X] (ν π : FinDist X) : ℝ :=
  (∑ x, ν.prob x ^ 2 / π.prob x) - 1
end Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
