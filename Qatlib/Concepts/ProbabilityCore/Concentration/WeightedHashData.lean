/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite averages and complex hash buckets

`finiteHashAverage` normalizes a sum over a finite seed type, and `weightedHashBucket` sums
complex weights over a hash fiber. These definitions supply the scalar data for later hash
moment and vector deviation estimates.

Aggregating complex weights is also a basic operation in sampling based matrix arithmetic; see
[ChiaEtAl2022] for that broader setting.

## Main statements

* `finiteHashAverage`: the normalized sum over hash seeds.
* `weightedHashBucket`: the complex mass of a hash bucket.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- The sum of a real function over a finite type multiplied by the reciprocal cardinality. -/
noncomputable def finiteHashAverage {H : Type} [Fintype H] (f : H → ℝ) : ℝ :=
  (Fintype.card H : ℝ)⁻¹ * ∑ r : H, f r

/-- The sum of complex weights of inputs mapped to a specified bucket by a specified hash seed. -/
noncomputable def weightedHashBucket {H X A : Type}
    [Fintype X] [DecidableEq A]
    (hash : H → X → A) (f : X → ℂ) (r : H) (a : A) : ℂ :=
  ∑ x : X, if hash r x = a then f x else 0

end Qatlib.Concepts.ProbabilityCore.Concentration
