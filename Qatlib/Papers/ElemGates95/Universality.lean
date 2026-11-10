/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.MultibitNetworks
import Qatlib.Concepts.GateTables.GrayUniversal.Section8GrayUniversalityElem
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.ElemGates95.Universality

theorem section8_universality (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Reg n) (Reg n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ 2 ^ (n - 1) * (2 ^ n + 1) * ((2 * n - 1) * (256 * n ^ 2 + 2 * n - 2)) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ =
          Matrix.mulVec U ψ :=
  Qatlib.Concepts.GateTables.GrayUniversal.section8GrayUniversality n hn U hU

end Qatlib.Papers.ElemGates95.Universality
