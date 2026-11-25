/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

@[expose] public section

/-!
# Variance control of the failure probability

Lemma 5.1 of the paper estimates the mean and the variance of the purity statistic and then turns
the variance bound into a failure probability of `1/100` at the paper's `.99` confidence level.
The passage from variance to failure probability is the finite Chebyshev inequality of
`Qatlib.Concepts.ProbabilityCore.Concentration.chebyshev`; this module records that passage once,
so that every variance estimate in Sections 4 and 5 can be used at the paper's confidence level
without repeating the arithmetic.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Lemma 5.1 and Eqs. (5.1)–(5.2).
-/

set_option autoImplicit false

namespace Qatlib.Papers.StateTesting26.MainResults

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- If the variance of `f` under the finite law `p` is at most `δ²/100`, then the deviations of
`f` from its mean by at least `δ` have probability at most `1/100`. -/
theorem eventMass_deviation_le_of_variance {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (h : p.variance f / δ ^ 2 ≤ 1 / 100) :
    eventMass p (fun x => δ ≤ |f x - p.expect f|) ≤ 1 / 100 :=
  (chebyshev p f δ hδ).trans h

end Qatlib.Papers.StateTesting26.MainResults
