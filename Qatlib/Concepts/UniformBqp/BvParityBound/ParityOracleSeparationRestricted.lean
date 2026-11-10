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
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.UniformBqp.BvParityBound

open Qatlib

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
