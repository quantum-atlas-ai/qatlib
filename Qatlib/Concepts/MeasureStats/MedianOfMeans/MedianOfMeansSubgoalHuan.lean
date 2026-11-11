/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MeasureStats.MedianOfMeans.MedianOfMeansSubgoalStat

/-!
# Median-of-means concentration

`medianOfMeansSubgoal` proves the finite-distribution concentration statement
`MedianOfMeansSubgoal` by applying the median-of-means estimate and the prescribed failure
budget. This is the statistical amplification used in classical-shadow estimation. See
[HuangKuengPreskill2020].

## Main statements

* `medianOfMeansSubgoal`: the variance and block-count budgets imply the required failure bound.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

namespace Qatlib.Concepts.MeasureStats.MedianOfMeans

open Qatlib

/-- The median-of-means failure probability is at most `δ` under the variance budget and the
block-count bound in `MedianOfMeansSubgoal`. -/
theorem medianOfMeansSubgoal : MedianOfMeansSubgoal := fun
  X _ _ p f L M hL hM ε δ hε hδ hvar hMδ =>
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.median_of_means_concentration p f hL hM ε hε hvar).trans hMδ

end Qatlib.Concepts.MeasureStats.MedianOfMeans
