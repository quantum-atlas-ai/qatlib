/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverCorrectedOracle

/-!
# State-preparation lower-bound specification

The proposition `InitialStatePreparationLowerBoundSubgoalCorrected` specifies a query lower
bound for unitary circuits that approximate every marked-instance solution using the corrected
preparation oracle. It uses an explicit error threshold and a finite-cardinality hypothesis.
Related mathematical background is given in [LowSu2026].

## Main statements

* `InitialStatePreparationLowerBoundSubgoalCorrected`: The instance cardinality is at most 64
  times the squared query count.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Matrix

/-- The assertion that uniformly accurate corrected-oracle solution preparation, at error at
most `1 / 100` and index cardinality at least 150, forces the cardinality to be at most 64
times the squared query count of the unitary circuit. -/
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
