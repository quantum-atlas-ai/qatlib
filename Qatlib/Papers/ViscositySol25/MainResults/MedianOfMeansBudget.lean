/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

@[expose] public section

/-!
# Finite-law median-of-means budget for the minimiser-function readout

*Quantum algorithms for viscosity solutions to nonlinear Hamilton-Jacobi equations based on an
entropy penalisation method*, arXiv:2512.07919v2, §IV.D.1, Lemma 20 and Eqs. (76)-(77). See
<https://arxiv.org/abs/2512.07919>.

The expectation `⟨u(t)|f(x̂)|u(t)⟩` of the minimiser function is estimated by a finite number of
independent preparations, and the paper splits the total readout error into a discretisation
budget `εmin` and a statistical budget `εf − εmin`. The variance of the estimator is bounded by
`Lterms * maxg`, the number of polynomial terms times the largest single-term second moment. This
file supplies the statistical step in finite-law form: once the mean block variance fits the
median-of-means threshold `4 * (Lterms * maxg) ≤ samples * (εf − εmin)²`, the failure mass of the
`blocks`-block median-of-means estimator is at most the tail bound `3 ^ (blocks / 2) / 2 ^ blocks`,
hence at most any `δ` above it.

The concentration theorem itself is the published finite-distribution estimate
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.median_of_means_concentration`; this module
only instantiates its block count, block size and threshold from the paper's budget data.

## Boundary

The estimate is purely statistical and finite-law. It does not construct the quantum sampler
that produces the samples, does not derive `Lterms * maxg` from the Hermitian term decomposition
`f = ∑ αᵢ gᵢ`, and says nothing about the discretisation error `εmin` beyond treating it as a
parameter of the gap `εf − εmin`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ViscositySol25.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **Lemma 20, Eqs. (76)-(77), p.22: the statistical budget step.**

Let `p` be a finite law on `ι`, `f` the readout observable, `Lterms * maxg` a variance budget for
`f`, and `εf − εmin > 0` the statistical error budget. If `samples` samples per block satisfy
`4 * (Lterms * maxg) ≤ samples * (εf − εmin)²` and `blocks` blocks satisfy
`3 ^ (blocks / 2) / 2 ^ blocks ≤ δ`, then the total probability of the `blocks`-block
median-of-means estimator of `expect f` deviating by more than `εf − εmin` is at most `δ`.

This is the variance-to-success composition of the paper's Lemma 20 copy count with the published
finite-law concentration bound; both `samples` and `blocks` are positive and the variance
hypothesis is kept as an explicit parameter. -/
theorem median_of_means_failure_prob_le_of_variance_budget
    {ι : Type*} [Fintype ι] [DecidableEq ι] {samples blocks : ℕ}
    (p : FinDist ι) (f : ι → ℝ) (Lterms maxg εf εmin δ : ℝ)
    (hsamples : 0 < samples) (hblocks : 0 < blocks) (hgap : 0 < εf - εmin)
    (hvar : p.variance f ≤ Lterms * maxg)
    (hbudget : 4 * (Lterms * maxg) ≤ (samples : ℝ) * (εf - εmin) ^ 2)
    (hδ : 3 ^ (blocks / 2) / 2 ^ blocks ≤ δ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin blocks → Fin samples → ι =>
        (εf - εmin) < |p.medianOfMeans f ω - p.expect f|),
      ∏ m, p.probOf (ω m) ≤ δ := by
  have hvar4 : 4 * p.variance f ≤ (samples : ℝ) * (εf - εmin) ^ 2 := by
    nlinarith [hvar, hbudget]
  exact (p.median_of_means_concentration f hsamples hblocks (εf - εmin) hgap hvar4).trans hδ

end Qatlib.Papers.ViscositySol25.MainResults
