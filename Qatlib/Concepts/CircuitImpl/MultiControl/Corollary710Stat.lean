/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Statement of the multi-controlled special-unitary bound

`Corollary7_10` expresses the multi-controlled special-unitary synthesis result associated with
[BarencoEtAl1995]. For distinct controls, target, and spectator as specified, it asks for an
exact target-fibre implementation with length at most `240 * (m + 2)`, zero queries, and
compiled gate count equal to word length.

## Main statements

* `Corollary7_10`: The proposition specifying linear-size synthesis of a controlled
  determinant-one qubit unitary.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

/-- The proposition that an `m`-controlled qubit unitary of determinant one, with a separate
spectator wire, has a legal, query-free implementation of length at most `240 * (m + 2)`
that preserves the background register [Barenco et al., Corollary 7.10][BarencoEtAl1995]. -/
def Corollary7_10 : Prop :=
  ∀ (N m : ℕ) (c : ℕ → Fin N) (s t : Fin N),
    Set.InjOn c (Set.Iio m) → (∀ i < m, c i ≠ s) → (∀ i < m, c i ≠ t) → s ≠ t →
    ∀ (W : Matrix Bool Bool ℂ), W ∈ Matrix.unitaryGroup Bool ℂ → Matrix.det W = 1 →
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      gs.length ≤ 240 * (m + 2) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
            (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) m then W else 1) φ)

end Qatlib.Concepts.CircuitImpl.MultiControl
