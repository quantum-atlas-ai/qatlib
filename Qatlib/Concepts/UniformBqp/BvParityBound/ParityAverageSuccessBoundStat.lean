/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityClassicalLowerBound
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

/-!
# The average parity-success bound

This module defines `ParityAverageSuccessBound`, the aggregate success inequality for randomized
classical parity-secret recovery. One distribution on adaptive query trees must satisfy the
query bound uniformly over its support; this formulation captures the classical side of the
parity-oracle setting of [BernsteinVazirani1997].

## Main statements

* `ParityAverageSuccessBound`: the sum of recovery success probabilities over all secrets is at
  most `2 ^ T`.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

namespace Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib
open scoped BigOperators

/-- The proposition that, for all `n` and `T`, any probability distribution on Boolean query
trees bounded by `T` queries has recovery success probabilities summing to at most `2 ^ T`
over all `n`-bit parity secrets. -/
def ParityAverageSuccessBound : Prop :=
  ∀ (n T : ℕ) (P : PMF (BoolQueryTree (Reg n) (Reg n))),
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries P T →
    (∑ k : Reg n,
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb P (bvCharBit k) (fun output => output = k)).toReal)
      ≤ (2 : ℝ) ^ T

end Qatlib.Concepts.UniformBqp.BvParityBound
