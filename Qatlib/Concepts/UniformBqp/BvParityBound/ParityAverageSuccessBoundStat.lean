/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityClassicalLowerBound
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

namespace Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib
open scoped BigOperators

def ParityAverageSuccessBound : Prop :=
  ∀ (n T : ℕ) (P : PMF (BoolQueryTree (Reg n) (Reg n))),
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries P T →
    (∑ k : Reg n,
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb P (bvCharBit k) (fun output => output = k)).toReal)
      ≤ (2 : ℝ) ^ T

end Qatlib.Concepts.UniformBqp.BvParityBound
