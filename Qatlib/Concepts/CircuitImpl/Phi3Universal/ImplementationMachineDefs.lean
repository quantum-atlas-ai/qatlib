/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffectiveDefs
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

def MachineClock (k : ℕ) : ℕ := k

def reverseWord (gs : List FiniteGateCode) : List FiniteGateCode :=
  gs ++ finiteWordAdjoint gs

def fiveRoundCost (forwardCost : ℕ) : ℕ := 5 * forwardCost + 2 * forwardCost

end Qatlib.Concepts.CircuitImpl.Phi3Universal

end
