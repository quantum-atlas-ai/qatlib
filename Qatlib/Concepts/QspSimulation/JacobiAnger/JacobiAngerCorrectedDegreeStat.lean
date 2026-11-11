/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support

/-!
# Specification of the corrected Jacobi–Anger degree

`JacobiAngerCorrectedDegree` specifies the two bounds required of `lcCorrectedQ`: it must exceed
the time parameter by at least one and reduce the factorial tail expression to ε/8. These
conditions support the Jacobi–Anger truncation analysis for QSP Hamiltonian simulation
[LowChuang2017].

## Main statements

* `JacobiAngerCorrectedDegree`: The cutoff and tail conditions for τ ≥ 0 and 0 < ε ≤ 1.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.JacobiAnger

/-- The proposition that for τ ≥ 0 and 0 < ε ≤ 1, q = `lcCorrectedQ τ ε` satisfies 4τ^q/(2^q q!)
≤ ε/8 and τ + 1 ≤ q. -/
def JacobiAngerCorrectedDegree : Prop :=
  ∀ (τ ε : ℝ), 0 ≤ τ → 0 < ε → ε ≤ 1 →
    4 * τ ^ (lcCorrectedQ τ ε : ℝ) /
        (2 ^ (lcCorrectedQ τ ε : ℝ) * (lcCorrectedQ τ ε).factorial : ℝ) ≤ ε / 8 ∧
    τ + 1 ≤ (lcCorrectedQ τ ε : ℝ)

end Qatlib.Concepts.QspSimulation.JacobiAnger
