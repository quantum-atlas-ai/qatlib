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
