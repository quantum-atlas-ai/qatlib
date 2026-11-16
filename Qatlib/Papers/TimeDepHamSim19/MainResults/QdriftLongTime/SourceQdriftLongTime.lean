/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Papers.TimeDepHamSim19.MainResults.Model.TimeDepHamSimModel

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Qatlib.Papers.TimeDepHamSim19.MainResults
open MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators ENNReal

open Qatlib.Papers.TimeDepHamSim19.MainResults

open Qatlib.Papers.TimeDepHamSim19.MainResults.IsDivision

namespace Qatlib.Papers.TimeDepHamSim19.MainResults.QdriftLongTime

section

/-- The step-count corollary of Theorem 7 (arXiv:1906.07115, eq. (72)): if
`r ≥ 4 ‖H‖²_{∞,1} / ε` then the achieved error `4 ‖H‖²_{∞,1} / r` is at most `ε`.
This is the arithmetic content of ``it suffices to choose `r ≥ 4⌈‖H‖²_{∞,1}/ε⌉`''. -/
theorem source_theorem7_steps_suffice {s ε : ℝ} {r : ℕ} (hr : 0 < (r : ℝ)) (hε : 0 < ε)
    (h : 4 * s ^ 2 / ε ≤ (r : ℝ)) : 4 * s ^ 2 / (r : ℝ) ≤ ε :=
  four_mul_sq_div_le hr hε h

end

end Qatlib.Papers.TimeDepHamSim19.MainResults.QdriftLongTime
