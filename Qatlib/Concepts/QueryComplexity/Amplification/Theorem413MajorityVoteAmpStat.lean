/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote

/-!
# Statement of majority vote amplification

This module defines `Theorem4_13MajorityVoteAmplification`, a finite circuit formulation
associated with Theorem 4.13 of [BennettEtAl1997]. A unitary circuit with zero queries and
success at least 2/3 can be repeated an odd number of times to achieve majority success at least
1 − ε for every ε > 0, with gate count proportional to the number of copies.

## Main statements

* `Theorem4_13MajorityVoteAmplification`: the proposition specifying majority amplification and
  exact gate cost.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Amplification

open Qatlib

/-- The statement that a unitary circuit with zero queries and success probability at least 2/3
can be repeated an odd number of times to achieve majority success at least 1 − ε for any ε
> 0, with gate count multiplied by the copy count. -/
def Theorem4_13MajorityVoteAmplification : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (C : Circuit I) (x₀ : I) (v : I → Bool)
    (b : Bool) (ε : ℝ),
    IsUnitaryCircuit C → QueryCount C = 0 →
      (2 / 3 : ℝ) ≤
        MeasureProb (Run 1 C (Ket x₀)) (Finset.univ.filter fun y => v y = b) →
      0 < ε →
        ∃ (r : ℕ) (C' : Circuit (Fin (2 * r + 1) → I)),
          IsUnitaryCircuit C' ∧ QueryCount C' = 0 ∧
            GateCount C' = (2 * r + 1) * GateCount C ∧
              1 - ε ≤
                MeasureProb (Run 1 C' (Ket fun _ => x₀))
                  (Finset.univ.filter fun ω => MajorityBit (fun j => v (ω j)) = b)

end Qatlib.Concepts.QueryComplexity.Amplification
