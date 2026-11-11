/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestrictedDefs

/-!
# A restricted parity-oracle separation statement

This module packages `ParityOracleSeparationRestricted`, combining exact one-query quantum
recovery, a two-query circuit identity, and the deterministic classical recovery lower bound.
The proposition states a restricted oracle separation in the setting of [BernsteinVazirani1997],
using the explicit circuits defined by the preceding module.

## Main statements

* `ParityOracleSeparationRestricted`: combines the one-query recovery equation, the two-query
  phase identity, and the `n`-query classical lower bound.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.UniformBqp.BvParityBound

open Qatlib

/-- The conjunction of exact one-query recovery of every parity secret from the
zero-register/minus-state input, the two-query identity implementing `PhaseOracle f ⊗
PauliZ`, and the `n`-query deterministic classical lower bound. -/
def ParityOracleSeparationRestricted : Prop :=
  (∀ (n : ℕ) (k : Reg n),
      Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
          (TensorState (Ket (ZeroStr n)) Minus)
        = TensorState (Ket k) Minus
      ∧ QueryCount (bvOneCallCircuit n) = 1)
  ∧ (∀ (n : ℕ) (f : Reg n → Bool) (ψ : QState (Reg n × Bool)),
      Run (BitOracleOn f) (bvTwoCallWord n) ψ
        = ApplyGate (TensorGate (PhaseOracle f) PauliZ) ψ
      ∧ QueryCount (bvTwoCallWord n) = 2)
  ∧ (∀ (n : ℕ) (T : BoolQueryTree (Reg n) (Reg n)),
      (∀ k : Reg n, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (bvCharBit k) T).1 = k) →
        n ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T)

end Qatlib.Concepts.UniformBqp.BvParityBound
