/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorODESystem

/-!
# Statement of the Taylor condition number bound

`Theorem5V2` packages the condition number estimate for the V2 history matrix. It specifies
diagonalizability, nonpositive real parts of diagonal entries, a unit operator-norm bound, and
the factorial condition on the Taylor degree. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `Theorem5V2`: The proposition asserting the condition number bound `6 * (‖V‖ * ‖V⁻¹‖) * k *
  (m+p)` for the V2 Taylor matrix under the stated stability, invertibility, degree, and
  factorial hypotheses.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition asserting the condition number bound `6 * (‖V‖ * ‖V⁻¹‖) * k * (m+p)` for the
V2 Taylor matrix under the stated stability, invertibility, degree, and factorial
hypotheses. -/
def Theorem5V2 : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (m k p : ℕ) (A V D : Matrix N N ℂ),
    0 < m → 5 ≤ k → 0 < p → Nat.factorial (k + 1) ≥ 2 * m →
    (∀ i j : N, i ≠ j → D i j = 0) →
    A = V * D * V⁻¹ → V * V⁻¹ = 1 → V⁻¹ * V = 1 →
    ‖A‖ ≤ 1 → (∀ i : N, (D i i).re ≤ 0) →
    ‖taylorStepMatrixV2 m k p A‖ * ‖(taylorStepMatrixV2 m k p A)⁻¹‖ ≤
      6 * (‖V‖ * ‖V⁻¹‖) * (k : ℝ) * ((m + p : ℕ) : ℝ)

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
