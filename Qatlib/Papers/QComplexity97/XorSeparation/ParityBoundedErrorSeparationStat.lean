/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityAverageSuccessBoundStat
import Qatlib.Papers.QComplexity97.XorSeparation.ParityOracleSeparationRestricted
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Papers.QComplexity97.XorSeparation
open Qatlib

def ParityBoundedErrorSeparation : Prop :=
  (∀ (n T : ℕ) (P : PMF (BoolQueryTree (Reg n) (Reg n))),
    BoolQueryTree.BoundedQueries P T →
    (∀ k : Reg n, (2 : ℝ) / 3 ≤
      (BoolQueryTree.SuccessProb P (bvCharBit k) (fun output => output = k)).toReal) →
    n ≤ T)
  ∧ (∀ n : ℕ,
    IsUnitaryCircuit (bvOneCallCircuit n) ∧
    Normalized (TensorState (Ket (ZeroStr n)) Minus) ∧
    QueryCount (bvOneCallCircuit n) = 1 ∧
    ∀ k : Reg n,
      MeasureProb
        (Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
          (TensorState (Ket (ZeroStr n)) Minus))
        ({k} ×ˢ (Finset.univ : Finset Bool)) = 1)

end Qatlib.Papers.QComplexity97.XorSeparation
