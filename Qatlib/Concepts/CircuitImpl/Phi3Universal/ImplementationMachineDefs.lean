/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffectiveDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Machine clocks and reversal costs

This module defines the clock and finite-word cost bookkeeping used by `ImplementationMachine`.
The word `reverseWord` executes a program followed by its adjoint, while `fiveRoundCost` records
five forward costs and two additional forward costs, as used in reversible quantum computation
[NielsenChuang2010].

## Main definitions

* `MachineClock`: the identity clock on natural-number step counts.
* `reverseWord`: a finite gate word followed by its adjoint word.
* `fiveRoundCost`: the cost `5*c + 2*c`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

/-- The identity clock assigning `k` machine steps to step count `k`. -/
def MachineClock (k : ℕ) : ℕ := k

/-- A finite gate word followed by its adjoint word. -/
def reverseWord (gs : List FiniteGateCode) : List FiniteGateCode :=
  gs ++ finiteWordAdjoint gs

/-- The cost ledger consisting of five forward costs and two additional forward costs. -/
def fiveRoundCost (forwardCost : ℕ) : ℕ := 5 * forwardCost + 2 * forwardCost

end Qatlib.Concepts.CircuitImpl.Phi3Universal

end
