/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma311
import Qatlib.Papers.QLattice03.MainResults.Reductions

/-!
# Two-point coefficient recovery specification

The proposition `twoPoint_recovers_coefficient` specifies a reduction from a two-point solver to
a unique shortest vector solver. Its uniqueness factor is a positive constant times the
dimension raised to `svpExponent f`. See [Regev2004] for the paper context.

## Main statements

* `twoPoint_recovers_coefficient`: The proposition that, for every positive `cunq`, a two-point
  solver at parameter `f` yields a solver satisfying `SolvesUniqueSVP` with factor `cunq *
  n^svpExponent f`.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

/-- The proposition that, for every positive `cunq`, a two-point solver at parameter `f` yields
a solver satisfying `SolvesUniqueSVP` with factor `cunq * n^svpExponent f`. -/
def twoPoint_recovers_coefficient (f : ℝ) : Prop :=
  ∀ (cunq : ℝ), 0 < cunq → HasTwoPointSolver f →
    ∃ B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ),
      SolvesUniqueSVP (fun n => cunq * (n : ℝ) ^ svpExponent f) B

end Qatlib.Papers.QLattice03.MainResults
