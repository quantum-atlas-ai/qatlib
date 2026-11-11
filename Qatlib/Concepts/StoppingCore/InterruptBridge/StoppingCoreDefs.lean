/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution

/-!
# Resumable quantum execution configurations

`QuantumContinuation` pairs a quantum state with its remaining circuit. The operations
`quantumTick` and `quantumRunFor` execute gates and oracle queries while retaining a
continuation, and `zeroCountdownNext` provides a deterministic two-step halting example.

The state-vector circuit semantics follow the quantum computation framework of
[NielsenChuang2010].

## Main statements

* `QuantumContinuation`: remaining circuit and current state
* `quantumTick`: one gate or query transition
* `quantumRunFor`: bounded iteration of quantum transitions

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

/-- A resumable quantum configuration containing the remaining circuit and the current quantum
state. -/
structure QuantumContinuation (I : Type*) where
  remaining : Circuit I
  state : QState I

/-- Execute the first remaining gate or oracle query, preserving configurations whose circuit is
empty. -/
def quantumTick {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) :
    QuantumContinuation I → QuantumContinuation I
  | ⟨[], ψ⟩ => ⟨[], ψ⟩
  | ⟨.gate U :: cs, ψ⟩ => ⟨cs, ApplyGate U ψ⟩
  | ⟨.query :: cs, ψ⟩ => ⟨cs, ApplyGate O ψ⟩

/-- Execute at most the given number of quantum steps on a continuation. -/
def quantumRunFor {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) :
    ℕ → QuantumContinuation I → QuantumContinuation I
  | 0, cfg => cfg
  | k+1, cfg => quantumRunFor O k (quantumTick O cfg)

/-- The deterministic Boolean countdown that moves from true to false and then halts with the
unit output. -/
def zeroCountdownNext (s : Bool) : PMF (Unit ⊕ Bool) :=
  if s then PMF.pure (.inr false) else PMF.pure (.inl ())

end Qatlib.Concepts.StoppingCore.InterruptBridge
