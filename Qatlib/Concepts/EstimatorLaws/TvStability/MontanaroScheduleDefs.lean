/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Finite Gibbs partition and divergence definitions

Introduces the finite Gibbs partition function and the algebraic chi-squared divergence
expression used in the cooling-schedule estimates of [Montanaro2015]. These definitions use
finite sums; positivity conditions are imposed by the later contracts that interpret their
ratios.

## Main statements

* `partitionFn` sums `exp (-β * H x)` over the finite state space.
* `chiSqDist` is the sum of `ν(x)² / π(x)` minus one.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The finite Gibbs partition function `∑ x, exp (-β * H x)` for a natural-valued energy
function. -/
noncomputable def partitionFn {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β : ℝ) : ℝ :=
  ∑ x : Ω, Real.exp (-(β * (H x : ℝ)))
end Qatlib.Concepts.EstimatorLaws.TvStability

namespace Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

/-- The finite chi-squared divergence expression `∑ x, ν(x)² / π(x) - 1`, defined without a
strict-positivity assumption on the denominator law. -/
noncomputable def chiSqDist {X : Type} [Fintype X] (ν π : FinDist X) : ℝ :=
  (∑ x, ν.prob x ^ 2 / π.prob x) - 1
end Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
