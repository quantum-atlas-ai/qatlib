/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# A finite median-of-means specification

`MedianOfMeansSubgoal` specifies a tail bound for independent blocks of samples from a finite
distribution. A variance budget fixes the samples per block, and a separate block-count budget
bounds the total failure probability. See [HuangKuengPreskill2020].

## Main statements

* `MedianOfMeansSubgoal`: the finite median-of-means concentration proposition.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.MeasureStats.MedianOfMeans

/-- The proposition that positive block sizes and tolerance satisfying `4 * p.variance f ≤ L * ε
^ 2` and `3 ^ (M / 2) / 2 ^ M ≤ δ` give median-of-means failure probability at most `δ`. -/
def MedianOfMeansSubgoal : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (f : X → ℝ)
    (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (ε δ : ℝ), 0 < ε → 0 < δ →
    4 * p.variance f ≤ (L : ℝ) * ε ^ 2 →
    3 ^ (M / 2) / 2 ^ M ≤ δ →
    ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin M → Fin L → X => ε < |p.medianOfMeans f ω - p.expect f|),
      ∏ m, p.probOf (ω m) ≤ δ

end Qatlib.Concepts.MeasureStats.MedianOfMeans
