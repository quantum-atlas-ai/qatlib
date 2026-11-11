/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# Statement of the symmetric zero error lower bound

This module defines `SymmetricZeroErrorQueryLowerBound` for finite Boolean inputs and auxiliary
workspaces. It states N + 1 ≤ 4Q for a nonconstant symmetric Boolean function when the two
outcome events never give an incorrect answer and their total probability is at least 1/2 on
every input, following [BealsEtAl2001].

## Main statements

* `SymmetricZeroErrorQueryLowerBound`: the proposition specifying the symmetric zero error query
  bound.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

/-- The statement that a nonconstant symmetric Boolean function requires input size plus one to
be at most four times the query count when the two outcome events never give a wrong answer
and have total probability at least 1/2. -/
def SymmetricZeroErrorQueryLowerBound : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit (Qatlib.Concepts.QueryWordCore.QueryMachinery.PolynomialWorkspace I W))
    (ψ : Qatlib.Foundations.PureStateMath.QState (PolynomialWorkspace I W))
    (E0 E1 : Finset (PolynomialWorkspace I W)) (f : (I → Bool) → Bool),
    (∀ x y : I → Bool, Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight x = Qatlib.Concepts.QueryComplexity.DegreeMethod.boolWeight y → f x = f y) →
    (∃ x y : I → Bool, f x ≠ f y) →
    (∀ x : I → Bool, f x = false →
        Qatlib.Foundations.PureStateMath.MeasureProb
          (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn x) 1) C ψ) E1
          = 0) →
    (∀ x : I → Bool, f x = true →
        Qatlib.Foundations.PureStateMath.MeasureProb
          (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn x) 1) C ψ) E0
          = 0) →
    (∀ x : I → Bool,
        (1 : ℝ) / 2 ≤
          Qatlib.Foundations.PureStateMath.MeasureProb
              (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn x) 1) C ψ) E0
            + Qatlib.Foundations.PureStateMath.MeasureProb
              (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn x) 1) C ψ) E1) →
    Fintype.card I + 1 ≤ 4 * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C

end Qatlib.Concepts.QueryComplexity.AdversarySearch
