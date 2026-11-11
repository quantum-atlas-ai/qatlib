/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound

/-!
# Hamming-layer symmetrization statement

This module defines `SymmetrizationAverageSubgoal`, the assertion that Hamming-layer averages of
any real multivariate polynomial are represented on all integer weights by a univariate
polynomial of no larger degree. It isolates the symmetrization property used by the polynomial
method [BealsEtAl2001].

## Main definitions

* `SymmetrizationAverageSubgoal`: existence of a degree-bounded polynomial representing all
  Hamming-layer averages.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The assertion that Hamming-layer averages of every real multivariate polynomial have a
univariate representation whose degree is bounded by the original total degree. -/
def SymmetrizationAverageSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (p : MvPolynomial I ℝ),
    ∃ q : Polynomial ℝ,
      (∀ k : ℕ, k ≤ Fintype.card I →
        Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k = Polynomial.eval (k : ℝ) q) ∧
        Polynomial.natDegree q ≤ p.totalDegree

end Qatlib.Concepts.QueryComplexity.DegreeMethod
