/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.TaylorODESystem
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

def Theorem7V2 : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (m k p : ℕ) (A V D : Matrix N N ℂ)
      (h g : ℝ) (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N)),
    0 < m → 5 ≤ k → 0 < p → 0 < h → 1 ≤ g →
    (∀ i j : N, i ≠ j → D i j = 0) →
    A = V * D * V⁻¹ → V * V⁻¹ = 1 → V⁻¹ * V = 1 →
    (∀ i : N, (D i i).re ≤ 0) → ‖h • A‖ ≤ 1 →
    0 < ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖ →
    70 * (‖V‖ * ‖V⁻¹‖) * (m : ℝ) *
        (‖stateVector x_in‖ + (m : ℝ) * h * ‖stateVector b‖) ≤
      ((Nat.factorial (k + 1) : ℕ) : ℝ) * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖ →
    (∀ t : ℝ, 0 ≤ t → t ≤ (m : ℝ) * h →
      ‖stateVector (taylorODESolution A b x_in t)‖ ≤
        g * ‖stateVector (taylorODESolution A b x_in ((m : ℝ) * h))‖) →
    taylorStepMatrixV2 m k p (h • A) *ᵥ x = taylorRHS m k p h x_in b →
    ∀ (j : ℕ) (hjp : j ≤ p),
      1 / Real.sqrt ((p : ℝ) + 77 * (m : ℝ) * g ^ 2) * ‖stateVector x‖ ≤
        ‖stateVector (taylorBlock x (taylorFinalLabel m k p j hjp))‖

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
