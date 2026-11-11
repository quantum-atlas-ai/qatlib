/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification

/-!
# The approximate polynomial block sensitivity statement

This module defines `ApproximatePolynomialBlockSensitivity`, the quantitative relation between
block sensitivity and the degree of a bounded approximating polynomial. The statement is a
component of the polynomial method for total Boolean functions [BealsEtAl2001].

## Main statements

* `ApproximatePolynomialBlockSensitivity`: for approximation error `ε < 1 / 2`, bounds `(1 - 2 *
  ε) * blockSensitivity f` by `(2 - 2 * ε) * p.totalDegree ^ 2`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators

/-- The statement that every polynomial with Boolean cube values in `[0, 1]` approximating `f`
within `0 ≤ ε < 1 / 2` satisfies `(1 - 2 * ε) * blockSensitivity f ≤ (2 - 2 * ε) *
p.totalDegree ^ 2`. -/
def ApproximatePolynomialBlockSensitivity : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (p : MvPolynomial (Fin n) ℝ) (ε : ℝ),
    0 ≤ ε → ε < 1/2 →
    (∀ x : Fin n → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1 ∧
      |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p -
        (if f x then (1 : ℝ) else 0)| ≤ ε) →
    (1 - 2 * ε) * (blockSensitivity f : ℝ) ≤
      (2 - 2 * ε) * (p.totalDegree : ℝ)^2

end Qatlib.Concepts.QueryComplexity.DegreeMethod
