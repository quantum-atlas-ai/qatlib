/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedDefinitions

/-!
# Corrected signed LCU success-fiber contract

`Theorem3LCUFiberCorrected` states the all-false ancilla output identity for the corrected
circuit associated with Theorem 3 of [ChildsWiebe2012]. For `k ≥ 1`, unitary branches, and
nonzero coefficients with both signs present, the fiber is the signed operator sum applied to
the input and divided by the total absolute coefficient mass.

## Main statements

* `Theorem3LCUFiberCorrected`: specifies the normalized signed-sum success fiber.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.LCUDeferred
open Matrix

/-- The proposition that the corrected protocol success fiber equals the signed operator sum
applied to the input, divided by the sum of absolute coefficients. It assumes `k ≥ 1`,
unitary branches, nonzero coefficients, and the presence of both coefficient signs [Childs
and Wiebe, Theorem 3][ChildsWiebe2012]. -/
def Theorem3LCUFiberCorrected : Prop :=
  ∀ (k : ℕ) (I : Type) [Fintype I] [DecidableEq I], 1 ≤ k →
    ∀ (U : Fin (k+1) → Matrix I I ℂ), (∀ q, U q ∈ Matrix.unitaryGroup I ℂ) →
      ∀ (c : Fin (k+1) → ℝ), (∀ q, c q ≠ 0) → (∃ q, 0 < c q) → (∃ q, c q < 0) →
        ∀ ψ : QState I, ∀ x : I,
          cwOutputCorrected k c U ψ (cwZero k, x)
            = (((∑ q, c q • U q)) *ᵥ ψ) x / (∑ q, |c q|)

end Qatlib.Papers.HamLCUSim12.LCUDeferred
