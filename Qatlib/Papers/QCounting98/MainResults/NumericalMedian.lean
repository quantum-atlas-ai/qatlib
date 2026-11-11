/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.FoldedEstimate

/-!
# Numerical medians for counting repetition

`sortedMedian_close_of_bad_le` controls a numerical median when at most half the samples are
inaccurate. Threshold consequences and `source_count_median_failure` give deterministic stopping
tests and an exponential failure bound for repeated counting estimates. The mathematical context
is [BrassardHoyerTapp1998Counting].

## Main statements

* `sortedMedian_close_of_bad_le`: If at most `r` of `2r + 1` samples lie farther than
  nonnegative `ε` from `μ`, their sorted median lies within `ε` of `μ`.
* `source_count_median_failure`: If a single scaled counting estimate has error probability at
  most `1/3`, the median of `2r + 1` independent estimates has error probability at most
  `(8/9)^r`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults.NumericalMedian

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.QCounting98.MainResults.ActualCounting

/-- If at most `r` of `2r + 1` samples lie farther than nonnegative `ε` from `μ`, their sorted
median lies within `ε` of `μ`. See [BrassardHoyerTapp1998Counting]. -/
theorem sortedMedian_close_of_bad_le (r : ℕ) (v : Fin (2 * r + 1) → ℝ) (μ ε : ℝ)
    (hε : 0 ≤ ε)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    |sortedBlockMedian r v - μ| ≤ ε := by
  by_contra h
  push Not at h
  have hmaj := heterogeneous_sorted_median_majority_witness r v μ ε hε h
  omega

/-- If at most `r` samples are inaccurate and `τ + ε < μ`, the sorted median of `2r + 1` samples
exceeds `τ`. See [BrassardHoyerTapp1998Counting]. -/
theorem median_threshold_decides_above (r : ℕ) (v : Fin (2 * r + 1) → ℝ) (μ ε τ : ℝ)
    (hε : 0 ≤ ε) (hμ : τ + ε < μ)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    τ < sortedBlockMedian r v := by
  have hclo := sortedMedian_close_of_bad_le r v μ ε hε hbad
  have h1 := (abs_le.mp hclo).1
  linarith

/-- If at most `r` samples are inaccurate and `μ + ε < τ`, the sorted median of `2r + 1` samples
is below `τ`. -/
theorem median_threshold_decides_below (r : ℕ) (v : Fin (2 * r + 1) → ℝ) (μ ε τ : ℝ)
    (hε : 0 ≤ ε) (hμ : μ + ε < τ)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    sortedBlockMedian r v < τ := by
  have hclo := sortedMedian_close_of_bad_le r v μ ε hε hbad
  have h2 := (abs_le.mp hclo).2
  linarith

/-- If a single scaled counting estimate has error probability at most `1/3`, the median of `2r
+ 1` independent estimates has error probability at most `(8/9)^r`. See
[BrassardHoyerTapp1998Counting]. -/
theorem source_count_median_failure (N P r : ℕ)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin P))
    (μ ε : ℝ) (hε : 0 ≤ ε)
    (hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
      (fun z => ε < |(N : ℝ) * foldedEstimate P z - μ|) ≤ 1 / 3) :
    p.probEvent (fun ω : Fin (2 * r + 1) → Fin P => ε <
      |sortedBlockMedian r (fun k => (N : ℝ) * foldedEstimate P (ω k)) - μ|)
      ≤ (8 / 9 : ℝ) ^ r := by
  exact Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure
    p (fun z => (N : ℝ) * foldedEstimate P z) r μ ε hε hb

/-- The numerical median exceeds the stopping threshold whenever at most `r` of `2r + 1` samples
are inaccurate and the true value exceeds the threshold by more than `ε`. See
[BrassardHoyerTapp1998Counting]. -/
theorem countrel_frequency_test_fires (r : ℕ) (v : Fin (2 * r + 1) → ℝ)
    (μ ε τ : ℝ) (hε : 0 ≤ ε) (hμ : τ + ε < μ)
    (hbad : (Finset.univ.filter fun j => ε < |v j - μ|).card ≤ r) :
    τ < sortedBlockMedian r v :=
  median_threshold_decides_above r v μ ε τ hε hμ hbad

end Qatlib.Papers.QCounting98.MainResults.NumericalMedian
