/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.AlgorithmicInterface
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.PowerSemidirect
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.Solver

/-!
# A query-bound result for diagonal power semidirect products

`theorem11_powerSemidirect` establishes `HasPolynomialQueryHSPSolver` for `PprM`, the semidirect
product formed using a diagonal unit action. The query predicate is measured in the cardinality
of a finite encoding, and the proof applies the general solver available in that interface. See
[InuiLeGall2007] for the mathematical setting.

## Main statements

* `theorem11_powerSemidirect`: establishes the finite-encoding query predicate for the power
  semidirect product.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem11

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

/-- For prime `p`, `r ≥ 1`, and a unit satisfying `u ^ p = 1`, the diagonal power semidirect
product satisfies `HasPolynomialQueryHSPSolver`, measured in finite-encoding token
cardinality. See [Inui and Le Gall, 2007, Theorem 11][InuiLeGall2007]. -/
theorem theorem11_powerSemidirect
    (m p r : ℕ) (_hp : p.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) :
    HasPolynomialQueryHSPSolver (PprM m p r u hu) :=

  hasPolynomialQueryHSPSolver _

end Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem11
