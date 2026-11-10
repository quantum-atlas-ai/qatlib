/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.AlgorithmicInterface
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.Solver
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem9

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

theorem theorem9_blackBox
    (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) :
    HasPolynomialQueryHSPSolver
      (Ppr p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr)) :=

  hasPolynomialQueryHSPSolver _

end Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem9
