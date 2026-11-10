/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV
set_option warningAsError false
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.NumericalWord.MixedWordError
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.NumericalWord.MixedWordError

def ValidControls {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : Prop :=
  ∀ s∈W, match s with | .known _ _ => True | .call _ _ none => True | .call _ _ (some (c,_)) => w≤c.val
noncomputable def step {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S→Matrix (Reg w) (Reg w) ℂ) (s : MixedStep n w S) : Matrix (Reg n) (Reg n) ℂ :=
  match s with | .known g k => numericalGateMatrix k g | .call _ _ _ => mixedStepMatrix hw O s
noncomputable def word {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S→Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)) : Matrix (Reg n) (Reg n) ℂ :=
  (W.map (step hw O)).reverse.prod

noncomputable def budget {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℝ :=
  ((knownPrecs W).map (fun k => ((2:ℝ)⁻¹)^k)).sum

end Qatlib.Concepts.NumericalWord.MixedWordError
