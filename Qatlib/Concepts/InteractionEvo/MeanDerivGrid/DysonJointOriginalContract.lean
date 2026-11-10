/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
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

theorem dysonJointOriginalContract_false : ¬DysonJointOriginalContract :=
  dyson_joint_unparenthesized_contract_false
end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
