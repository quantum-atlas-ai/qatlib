/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashData
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Vector masses and centered hash deviations

The module defines the deviation of a complex bucket from its uniform share of the total weight.
For a finite family of weights, it sums the Euclidean component deviation norm over buckets and
records the total squared component mass.

These quantities use the finite vector norm framework of [Bhatia1997] for subsequent average
hash deviation estimates.

## Main statements

* `weightedHashDeviation`: centered complex bucket mass.
* `weightedHashVectorDeviation`: the sum of Euclidean deviation norms over buckets.
* `weightedHashVectorMass`: the total squared norm of all input component weights.

## References

* [Bhatia, 1997][Bhatia1997]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- The complex bucket mass minus the total complex input mass divided by the bucket
cardinality. -/
noncomputable def weightedHashDeviation {H X A : Type}
    [Fintype X] [Fintype A] [DecidableEq A]
    (hash : H → X → A) (f : X → ℂ) (r : H) (a : A) : ℂ :=
  weightedHashBucket hash f r a -
    (Fintype.card A : ℂ)⁻¹ * ∑ x : X, f x

/-- The sum over buckets of the square root of the sum of squared component hash deviations. -/
noncomputable def weightedHashVectorDeviation {H X A T : Type}
    [Fintype X] [Fintype A] [DecidableEq A] [Fintype T]
    (hash : H → X → A) (f : T → X → ℂ) (r : H) : ℝ :=
  ∑ a : A, Real.sqrt (∑ k : T, Complex.normSq
    (weightedHashDeviation hash (f k) r a))

/-- The sum of squared complex norms over all components and inputs. -/
noncomputable def weightedHashVectorMass {X T : Type}
    [Fintype X] [Fintype T] (f : T → X → ℂ) : ℝ :=
  ∑ k : T, ∑ x : X, Complex.normSq (f k x)

end Qatlib.Concepts.ProbabilityCore.Concentration
