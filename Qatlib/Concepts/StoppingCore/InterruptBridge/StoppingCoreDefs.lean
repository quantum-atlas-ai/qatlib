/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

structure QuantumContinuation (I : Type*) where
  remaining : Circuit I
  state : QState I

def quantumTick {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) :
    QuantumContinuation I → QuantumContinuation I
  | ⟨[], ψ⟩ => ⟨[], ψ⟩
  | ⟨.gate U :: cs, ψ⟩ => ⟨cs, ApplyGate U ψ⟩
  | ⟨.query :: cs, ψ⟩ => ⟨cs, ApplyGate O ψ⟩

def quantumRunFor {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) :
    ℕ → QuantumContinuation I → QuantumContinuation I
  | 0, cfg => cfg
  | k+1, cfg => quantumRunFor O k (quantumTick O cfg)

def zeroCountdownNext (s : Bool) : PMF (Unit ⊕ Bool) :=
  if s then PMF.pure (.inr false) else PMF.pure (.inl ())

end Qatlib.Concepts.StoppingCore.InterruptBridge
