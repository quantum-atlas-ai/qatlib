/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Amplification

open Qatlib

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
