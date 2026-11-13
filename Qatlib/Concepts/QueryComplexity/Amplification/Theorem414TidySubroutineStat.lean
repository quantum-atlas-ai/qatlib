/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Statement of tidy subroutine amplification

This module defines `Theorem4_14TidySubroutine`, a finite circuit cleaning statement associated
with Theorem 4.14 of [BennettEtAl1997]. For a unitary circuit with zero queries and success at
least 2/3, it requests a circuit that restores its input copies and produces the desired answer
with probability at least 1 − ε, using at most twice the repeated gate count plus one.

## Main statements

* `Theorem4_14TidySubroutine`: the proposition specifying restored input, answer probability,
  and gate budget.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Amplification

open Qatlib

/-- The statement that a unitary circuit with zero queries and success probability at least 2/3
can be converted, for any ε > 0, into a unitary circuit with zero queries that restores the
initial registers and outputs the desired bit with probability at least 1 − ε, within the
stated gate budget. -/
def Theorem4_14TidySubroutine : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (C : Circuit I) (x₀ : I) (v : I → Bool)
    (b : Bool) (ε : ℝ),
    IsUnitaryCircuit C → QueryCount C = 0 →
      (2 / 3 : ℝ) ≤
        MeasureProb (Run 1 C (Ket x₀)) (Finset.univ.filter fun y => v y = b) →
      0 < ε →
        ∃ (r : ℕ) (C' : Circuit ((Fin (2 * r + 1) → I) × Bool)),
          IsUnitaryCircuit C' ∧ QueryCount C' = 0 ∧
            GateCount C' ≤ 2 * ((2 * r + 1) * GateCount C) + 1 ∧
              1 - ε ≤
                MeasureProb (Run 1 C' (Ket (fun _ => x₀, false)))
                  {(fun _ => x₀, b)}

end Qatlib.Concepts.QueryComplexity.Amplification
