/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

def Corollary6_2 : Prop :=
  ∀ (N : ℕ) (c : ℕ → Fin N) (t : Fin N),
    Set.InjOn c (Set.Iio 2) → (∀ i < 2, c i ≠ t) →
    ∀ U : Matrix Bool Bool ℂ, U ∈ Matrix.unitaryGroup Bool ℂ →
    ∃ gs : List (ReflectionGate N),
      reflectionLegal gs ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      (gs.filter Sum.isLeft).length ≤ 8 ∧
      (gs.filter Sum.isRight).length ≤ 8 ∧
      ∀ (x : Reg N) (φ : QState Bool),
        Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (multiWireState t x φ) =
          multiWireState t x
            (ApplyGate (if noWorkPrefixAnd (fun i => x (c i)) 2 then U else 1) φ)

end Qatlib.Concepts.CircuitImpl.MultiControl
