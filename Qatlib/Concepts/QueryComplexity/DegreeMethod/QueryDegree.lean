/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound

/-!
# Exact and approximate Boolean polynomial degree

This module defines real polynomial evaluation on Boolean inputs and the exact and approximate
degrees of Boolean functions. The quantities `exactDegree` and `approxDegree` take infima of
total degrees, with uniform approximation tolerance `1 / 3` for the latter, as in the polynomial
method of [BealsEtAl2001].

## Main statements

* `boolEval`: Evaluates a polynomial at the zero-one point of a Boolean input.
* `exactDegree`: The infimum of degrees of exact representing polynomials.
* `approxDegree`: The infimum of degrees of polynomials approximating within `1 / 3`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Evaluates a real multivariate polynomial at the zero-one point corresponding to a Boolean
input. -/
noncomputable def boolEval (p : MvPolynomial I ℝ) (g : I → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p

/-- The natural-number infimum of total degrees of real polynomials exactly representing the
Boolean function. -/
noncomputable def exactDegree (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ g : I → Bool, boolEval p g = if f g then (1 : ℝ) else 0})

/-- The natural-number infimum of total degrees of real polynomials uniformly approximating the
Boolean function within `1 / 3`. -/
noncomputable def approxDegree (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ g : I → Bool, |boolEval p g - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3})

end Qatlib.Concepts.QueryComplexity.DegreeMethod
