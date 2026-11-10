/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma311
import Qatlib.Papers.QLattice03.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

def twoPoint_recovers_coefficient (f : ℝ) : Prop :=
  ∀ (cunq : ℝ), 0 < cunq → HasTwoPointSolver f →
    ∃ B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ),
      SolvesUniqueSVP (fun n => cunq * (n : ℝ) ^ svpExponent f) B

end Qatlib.Papers.QLattice03.MainResults
