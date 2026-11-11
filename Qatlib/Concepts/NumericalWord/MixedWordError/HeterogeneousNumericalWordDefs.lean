/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV

/-!
# Numerical mixed word semantics

Mixed words use numerical matrices for known gates and exact matrices for oracle calls.
`ValidControls` requires controlled calls to use auxiliary bits, and `budget` adds the dyadic
tolerances of known gates, providing data for circuit error estimates in the setting of
[NielsenChuang2010]

## Main statements

* `step` and `word`: define numerical matrix semantics for mixed words.
* `ValidControls`: restricts oracle controls to the auxiliary register.
* `budget`: sums known gate tolerances.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.NumericalWord.MixedWordError
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.NumericalWord.MixedWordError

/-- The condition that every controlled oracle call in the word uses a control index at least
`w`. -/
def ValidControls {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : Prop :=
  ∀ s∈W, match s with | .known _ _ => True | .call _ _ none => True | .call _ _ (some (c,_)) => w≤c.val
/-- The numerical gate matrix at the stored precision for a known step, or the exact mixed step
matrix for an oracle call. -/
noncomputable def step {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S→Matrix (Reg w) (Reg w) ℂ) (s : MixedStep n w S) : Matrix (Reg n) (Reg n) ℂ :=
  match s with | .known g k => numericalGateMatrix k g | .call _ _ _ => mixedStepMatrix hw O s
/-- The reverse ordered product of the numerical mixed step matrices. -/
noncomputable def word {n w : ℕ} (hw : w≤n) {S : Type}
    (O : S→Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)) : Matrix (Reg n) (Reg n) ℂ :=
  (W.map (step hw O)).reverse.prod

/-- The sum of `(1 / 2)^k` over the precision labels of the known gates in a mixed word. -/
noncomputable def budget {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℝ :=
  ((knownPrecs W).map (fun k => ((2:ℝ)⁻¹)^k)).sum

end Qatlib.Concepts.NumericalWord.MixedWordError
