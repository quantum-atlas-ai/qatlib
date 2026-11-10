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

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

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
