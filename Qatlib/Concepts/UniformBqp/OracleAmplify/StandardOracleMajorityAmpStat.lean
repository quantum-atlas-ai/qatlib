/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Standard-oracle majority amplification specification

`StandardOracleMajorityAmplification` specifies majority-vote error reduction for a family of
inputs sharing a unitary circuit and basis seed. The statement records the repetition bound,
exact routing costs, and success probability for the majority readout. The background is
described in [BennettEtAl1997].

## Main statements

* `StandardOracleMajorityAmplification`: the quantified majority amplification guarantee.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical BigOperators

/-- The assertion that a unitary bit-oracle circuit succeeding with probability at least `2/3`
can be amplified to success at least `1 - ε` by an odd number of routed copies and majority
vote. It includes a logarithmic repetition bound and exact query and gate counts. -/
def StandardOracleMajorityAmplification : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (W X : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    [Fintype X] [DecidableEq X] (C : Circuit ((Fin n × Bool) × W))
    (seed : (Fin n × Bool) × W) (v : ((Fin n × Bool) × W) → Bool)
    (input : X → Fin n → Bool) (b : X → Bool) (ε : ℝ),
    IsUnitaryCircuit C →
    (∀ x : X, (2 / 3 : ℝ) ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (input x)) C (Ket seed))
      (Finset.univ.filter fun z => v z = b x)) → 0 < ε →
    ∃ (r : ℕ) (D : Circuit
        ((Fin n × Bool) × (Fin (2 * r + 1) → (Fin n × Bool) × W))),
      r ≤ Nat.ceil (Real.log (1 / ε) / Real.log (9 / 8)) + 1 ∧
      IsUnitaryCircuit D ∧ QueryCount D = (2 * r + 1) * QueryCount C ∧
      GateCount D = (2 * r + 1) * GateCount C + 2 * (2 * r + 1) * QueryCount C ∧
      ∀ x : X, 1 - ε ≤ MeasureProb
        (Run (workspaceBitOracle (W := Fin (2 * r + 1) → (Fin n × Bool) × W)
          (input x)) D (Ket ((⟨0, hn⟩, false), fun _ => seed)))
        (Finset.univ.filter fun z => MajorityBit (fun j => v (z.2 j)) = b x)

end Qatlib.Concepts.UniformBqp.OracleAmplify
