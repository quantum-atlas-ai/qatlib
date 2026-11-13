/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.AlgorithmicInterface
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.Solver

/-!
# A query-bound result for the canonical cyclic semidirect product

`theorem9_blackBox` applies the finite-encoding solver interface to the canonical semidirect
product for an odd prime `p` and `r ≥ 2`. Its polynomial query bound is measured in token
cardinality, using the general solver construction. See [InuiLeGall2007] for the mathematical
setting.

## Main statements

* `theorem9_blackBox`: establishes `HasPolynomialQueryHSPSolver` for the canonical action.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem9

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

/-- For an odd prime `p` and `r ≥ 2`, the canonical cyclic semidirect product satisfies
`HasPolynomialQueryHSPSolver` with query bounds measured in token cardinality. See [Inui and
Le Gall, 2007, Theorem 9][InuiLeGall2007]. -/
theorem theorem9_blackBox
    (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    HasPolynomialQueryHSPSolver
      (Ppr p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr)) :=

  hasPolynomialQueryHSPSolver _

end Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem9
