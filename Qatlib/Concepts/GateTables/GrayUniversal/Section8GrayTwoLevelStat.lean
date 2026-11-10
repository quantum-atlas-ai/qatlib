/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal

def Section8GrayTwoLevel : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ g : TwoLevelInstruction (Reg n), twoLevelLegal g →
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ (2 * n - 1) * (256 * n ^ 2 + 2 * n - 2) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ =
          Matrix.mulVec (twoLevelMatrix g) ψ

end Qatlib.Concepts.GateTables.GrayUniversal
