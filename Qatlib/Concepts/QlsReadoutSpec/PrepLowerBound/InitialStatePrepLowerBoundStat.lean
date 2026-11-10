/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverCorrectedOracle
set_option warningAsError false

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Matrix

def InitialStatePreparationLowerBoundSubgoalCorrected : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (ν₀ : QState Bool) (ω₀ : QState W) (ε : ℝ) (C : Circuit ((I × Bool) × W)),
    150 ≤ Fintype.card I → ε ≤ 1 / 100 →
    IsUnitaryCircuit C → Normalized ν₀ → Normalized ω₀ →
    (∀ x : I,
      ‖stateVector (Run (bOracleCorrected (I := I) (W := W) x) C (solverStart ν₀ ω₀)) -
          stateVector (solutionTarget ν₀ ω₀ x)‖ ≤ ε) →
    (Fintype.card I : ℝ) ≤ 64 * ((QueryCount C : ℕ) : ℝ) ^ 2

end Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
