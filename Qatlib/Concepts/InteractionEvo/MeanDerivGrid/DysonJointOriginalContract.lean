/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid

/-!
# Failure of an unparenthesized Dyson error contract

This module defines `DysonJointOriginalContract` using an unparenthesized interval integral and
proves that proposition false. The integral scope places the factorial-tail expression inside
the integral, so this statement differs from the three-term error estimate used for the Dyson
analysis of [LowWiebe2018].

## Main statements

* `DysonJointOriginalContract`: the unparenthesized candidate error statement.
* `dysonJointOriginalContract_false`: refute that statement.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
/-- The candidate universal Dyson grid error bound whose unparenthesized integral includes the
factorial-tail summand in its integrand. -/
def DysonJointOriginalContract : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H Hd : ℝ → Matrix I I ℂ) (t Λ : ℝ) (M K : ℕ),
    Continuous H → 0 ≤ t → 0 ≤ Λ → 0 < M →
    (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian ∧ ‖H u‖ ≤ Λ) →
    Continuous Hd → (∀ u ∈ Set.Icc 0 t, HasDerivAt H (Hd u) u) →
    Λ * t ≤ Real.log 2 →
    ‖dysonGridTruncatedSum H t M K -
        orderedEvolution (fun u => Complex.I • H u) 0 t‖ ≤
      Real.exp (Λ * t) * Λ ^ 2 * t ^ 2 / (2 * M)
        + (t / M) * ∫ u in (0 : ℝ)..t, ‖Hd u‖
        + (2 : ℝ) * (Λ * t) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ)

/-- The unparenthesized candidate Dyson joint error contract is false. -/
theorem dysonJointOriginalContract_false : ¬DysonJointOriginalContract :=
  dyson_joint_unparenthesized_contract_false
end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
