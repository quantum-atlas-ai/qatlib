/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityStat
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalConsumers
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# The Gram-state preparation specification

This module defines `GramStatePreparationSubgoal`, a finite reflection-gate preparation
requirement for normalized weighted Gram states. An equivalence with an `n`-bit register
determines the relabeled target, and the specification bounds the legal reflection word used for
exact embedded preparation.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `GramStatePreparationSubgoal`: a legal reflection word of length at most `128 * (n + 1) ^ 2 *
  4 ^ n` preparing the embedded Gram state.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix

/-- The proposition that every normalized weighted Gram state, relabeled by the given register
equivalence, can be prepared exactly in the known-frame embedding by at most `128 * (n + 1)
^ 2 * 4 ^ n` legal reflection gates. -/
def GramStatePreparationSubgoal : Prop :=
  ∀ (r d n : ℕ) (e : Fin r × Fin d ≃ Reg n)
    (ψ : Fin r → QState (Fin d)), (∀ i, Normalized (ψ i)) →
    ∀ (w : Fin r → ℝ), (∀ i, 0 ≤ w i) → (∑ i, (w i) ^ 2 = 1) →
    ∃ gs : List (ReflectionGate (n + (n + 1))), reflectionLegal gs ∧
      gs.length ≤ 128 * (n + 1) ^ 2 * 4 ^ n ∧
      Run 1 (reflectionCompile gs) (knownFrameEmbed n (Qatlib.Foundations.PureStateMath.Ket (fun _ => false))) =
        knownFrameEmbed n (relabelState e (gramState ψ w))

end Qatlib.Concepts.CopyEvolution.SelfTomography
