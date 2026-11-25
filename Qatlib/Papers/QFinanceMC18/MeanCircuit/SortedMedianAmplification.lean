/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.SortedMedianGeneralDelta

@[expose] public section

/-!
# Lemma 6: median amplification of independent estimates

Lemma 6 of the fixed source repeats an estimate `2 * r + 1` times and keeps the sorted median.
Each estimate fails with probability at most `δ < 1 / 2`, and the median fails only when a
majority of the runs fail, so the failure probability is at most
`(1 / 2) * (2 * sqrt (δ * (1 - δ))) ^ (2 * r + 1)`. Theorems 2 and 3 of the source use this
amplification to convert a constant single-run confidence into an exponentially small one.

The binomial-tail content is proved once in
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.sorted_median_failure_general_delta`, and the
declarations here restate it for the paper's finite sampling model, expose the confidence
threshold reading, and record that the amplification base is strictly below one.

Boundary: the sampling model is a finite distribution over estimate outcomes sampled independently
`2 * r + 1` times; the amplitude-estimation law of Theorems 1 and 2 is not instantiated here, and
the `O (log (1 / η))` repetition count is only recorded through its defining threshold.

## Main statements

* `lemma_6_sorted_median_amplification`: the failure bound of Lemma 6.
* `lemma_6_repetitions_suffice`: `2 * r + 1` repetitions keep the final failure below `η`
  whenever the amplified bound is at most `η`.
* `median_amplification_base_lt_one`: below one-half single-run failure the amplification base
  `2 * sqrt (δ * (1 - δ))` is strictly smaller than one, so the bound decays geometrically.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QFinanceMC18.MeanCircuit.SortedMedianAmplification

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

/-- Lemma 6 of [RebentrostGuptBromley2018]: the sorted median of `2 * r + 1` independent
estimates whose single-run failure mass at threshold `ε` is at most `δ < 1 / 2` fails with
probability at most `(1 / 2) * (2 * sqrt (δ * (1 - δ))) ^ (2 * r + 1)`. -/
theorem lemma_6_sorted_median_amplification {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (v : X → ℝ) (r : ℕ) (μ ε δ : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ)
    (hδ2 : δ < 1 / 2) (hb : mass p (fun x => ε < |v x - μ|) ≤ δ) :
    p.probEvent (fun ω : Fin (2 * r + 1) → X =>
        ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|)
      ≤ (1 / 2) * (2 * Real.sqrt (δ * (1 - δ))) ^ (2 * r + 1) :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.sorted_median_failure_general_delta
    p v r μ ε δ hε hδ0 hδ2 hb

/-- The second clause of Lemma 6 in threshold form: if the amplified bound is at most the target
failure probability `η`, then `2 * r + 1` repetitions keep the median failure at most `η`. -/
theorem lemma_6_repetitions_suffice {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (v : X → ℝ) (r : ℕ) (μ ε δ η : ℝ) (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ)
    (hδ2 : δ < 1 / 2) (hb : mass p (fun x => ε < |v x - μ|) ≤ δ)
    (hη : (1 / 2) * (2 * Real.sqrt (δ * (1 - δ))) ^ (2 * r + 1) ≤ η) :
    p.probEvent (fun ω : Fin (2 * r + 1) → X =>
        ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|) ≤ η :=
  (lemma_6_sorted_median_amplification p v r μ ε δ hε hδ0 hδ2 hb).trans hη

/-- For a single-run failure probability `δ < 1 / 2`, the amplification base
`2 * sqrt (δ * (1 - δ))` is strictly below one, so the Lemma 6 bound decays geometrically in the
number of repetitions. -/
theorem median_amplification_base_lt_one {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ2 : δ < 1 / 2) :
    2 * Real.sqrt (δ * (1 - δ)) < 1 := by
  have hprod : 0 ≤ δ * (1 - δ) := by nlinarith
  have hsq : Real.sqrt (δ * (1 - δ)) ^ 2 = δ * (1 - δ) := Real.sq_sqrt hprod
  nlinarith [Real.sqrt_nonneg (δ * (1 - δ)), hsq]

end Qatlib.Papers.QFinanceMC18.MeanCircuit.SortedMedianAmplification
