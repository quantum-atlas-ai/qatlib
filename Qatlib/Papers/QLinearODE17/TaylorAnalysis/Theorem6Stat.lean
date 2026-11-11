/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorODESystem

/-!
# Statement of the Taylor solution error bound

`Theorem6V2` specifies a stable diagonalizable ODE, a bounded scaled generator, and a solution
of the V2 Taylor system. Its conclusion bounds every time-block error in the Euclidean norm by a
quantity inversely proportional to `(k+1)!`. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `Theorem6V2`: The proposition asserting the V2 time-block error bound `2.8 * (‖V‖ * ‖V⁻¹‖) * j
  * (‖x_in‖₂ + m*h*‖b‖₂) / (k+1)!` under the stated parameter, stability, and linear-system
  hypotheses.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition asserting the V2 time-block error bound `2.8 * (‖V‖ * ‖V⁻¹‖) * j * (‖x_in‖₂
+ m*h*‖b‖₂) / (k+1)!` under the stated parameter, stability, and linear-system hypotheses. -/
def Theorem6V2 : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (m k p : ℕ) (A V D : Matrix N N ℂ)
      (h : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N)),
    0 < m → 5 ≤ k → 0 < p → Nat.factorial (k + 1) ≥ 2 * m → 0 < h →
    (∀ i j : N, i ≠ j → D i j = 0) →
    A = V * D * V⁻¹ → V * V⁻¹ = 1 → V⁻¹ * V = 1 →
    (∀ i : N, (D i i).re ≤ 0) → ‖h • A‖ ≤ 1 →
    taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b →
    ∀ (j : ℕ) (hjm : j ≤ m),
      ‖stateVector (taylorODESolution A b x_in ((j : ℝ) * h)) -
          stateVector (taylorBlock x (taylorTimeLabel m k p j hjm))‖ ≤
        2.8 * (‖V‖ * ‖V⁻¹‖) * (j : ℝ) *
          (‖stateVector x_in‖ + (m : ℝ) * h * ‖stateVector b‖) / ((Nat.factorial (k + 1) : ℕ) : ℝ)

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
