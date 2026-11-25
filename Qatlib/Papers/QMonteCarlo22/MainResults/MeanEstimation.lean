/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

@[expose] public section

/-!
# Finite mean estimation with median amplification

This module proves a classical finite-distribution median-of-means baseline for
comparison with quantum mean estimation [Montanaro2015] and
[Kothari and O'Donnell](https://arxiv.org/abs/2208.07544v1). A `FinDist` is a law on a finite outcome type, and
`medianOfMeans` combines eight independent blocks, each containing `L > 0` independent draws.
For `ε > 0`, the variance condition `4 * Var(f) ≤ L * ε²` gives a failure-mass
bound of `81 / 256` using `8 * L` ordinary samples.

This guarantee uses a classical sampling model. It does not implement the
coherent access to the code or the quantum sample complexity of Theorem 1.1,
nor the promise distinguisher of Theorem 1.3.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMonteCarlo22.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **Finite classical median-of-means baseline.**

For a finite distribution and a real payoff, eight independent blocks of any positive
length have a median-of-means failure probability at most `1/3` whenever the block
variance budget is `4 * Var(f) ≤ L * ε²`.  The event and its mass are written out over
the finite sample space, so the conclusion is a genuine probability statement with no
implicit non-emptiness or asymptotic convention.
-/
theorem theorem_1_1_median_of_means
    {X : Type*} [Fintype X] [DecidableEq X]
    {L : ℕ} (p : FinDist X) (f : X → ℝ)
    (hL : 0 < L) (ε : ℝ) (hε : 0 < ε)
    (hvar : 4 * p.variance f ≤ (L : ℝ) * ε ^ 2) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin 8 → Fin L → X => ε <
          |p.medianOfMeans f ω - p.expect f|),
      ∏ m, p.probOf (ω m)) ≤ (1 : ℝ) / 3 := by
  have h := p.median_of_means_concentration f hL (by norm_num : 0 < (8 : ℕ)) ε hε hvar
  calc
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin 8 → Fin L → X => ε <
          |p.medianOfMeans f ω - p.expect f|),
      ∏ m, p.probOf (ω m))
        ≤ (3 : ℝ) ^ ((8 : ℕ) / 2) / (2 : ℝ) ^ 8 := h
    _ = (81 : ℝ) / 256 := by norm_num
    _ ≤ (1 : ℝ) / 3 := by norm_num

end Qatlib.Papers.QMonteCarlo22.MainResults
