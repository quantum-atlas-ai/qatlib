/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Statement of the conjunction-toggle bound

`Corollary7_4` states the elementary-gate form of the conjunction-toggle construction in
[BarencoEtAl1995]. It specifies at least five distinct controls, separate spectator and target
wires, legality, zero queries, a length bound of `48 * m - 108`, and exact basis-state
semantics.

## Main statements

* `Corollary7_4`: The proposition specifying the conjunction-controlled target toggle.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

/-- The proposition that a conjunction toggle with `m ≥ 5` distinct controls and separate
spectator and target wires has a legal, query-free implementation using at most `48 * m -
108` gates [Barenco et al., Corollary 7.4][BarencoEtAl1995]. -/
def Corollary7_4 : Prop :=
  ∀ (N m : ℕ) (c : ℕ → Fin N) (s t : Fin N),
    5 ≤ m → Set.InjOn c (Set.Iio m) → (∀ i < m, c i ≠ s) → (∀ i < m, c i ≠ t) →
    s ≠ t →
    ∃ gs : List (ReflectionGate N),
      reflectionLegal gs ∧
      gs.length ≤ 48 * m - 108 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ x : Reg N,
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) =
          Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m))

end Qatlib.Concepts.CircuitImpl.MultiControl
