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

This module gives a finite, source-faithful model for the mean-estimation setting of
[Montanaro2015] and QMonteCarlo22, Theorems 1.1 and 1.3.  A `FinDist` is an explicit
probability law on a finite outcome type, `avg` is the arithmetic mean of a non-empty
independent sample record, and `medianOfMeans` is the sorted median of eight independent
blocks.  The theorem below records the exact constant obtained from the finite Chebyshev
bound and the median amplification argument.

The statement is deliberately about the finite probability model represented by
`FinDist`.  It does not claim that a source-code oracle or a quantum circuit has been
constructed.  Those access and implementation bridges remain separate obligations of
the paper formalisation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMonteCarlo22.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- **QMonteCarlo22, Theorem 1.1 model.**

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
