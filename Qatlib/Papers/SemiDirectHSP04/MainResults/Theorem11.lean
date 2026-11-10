/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.AlgorithmicInterface
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.PowerSemidirect
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.Solver
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem11

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

theorem theorem11_powerSemidirect
    (m p r : ℕ) (_hp : p.Prime) (_hr : 1 ≤ r)
    (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) :
    HasPolynomialQueryHSPSolver (PprM m p r u hu) :=

  hasPolynomialQueryHSPSolver _

end Qatlib.Papers.SemiDirectHSP04.MainResults.Theorem11
