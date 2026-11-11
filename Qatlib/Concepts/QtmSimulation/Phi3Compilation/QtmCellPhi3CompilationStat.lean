/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.FiniteBasisPhi3PaddingStat

/-!
# The QTM window Φ3 compilation contract

This module states `QtmCellPhi3Compilation`, the contract for exact simulation of repeated
finite QTM window rounds by unitary Φ3 circuits. The contract records no oracle queries, a
concrete gate-list bound, and equality for every encoded state, in the circuit-simulation
setting of [Yao1993].

## Main statements

* `QtmCellPhi3Compilation`: The quantified encoding, circuit-cost, and state-simulation
  requirements.

## References

* [Yao, 1993][Yao1993]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile

namespace Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Matrix

/-- The proposition that every injectively encoded finite QTM window with unitary local update
has a zero-query unitary Φ3 simulation of `k` rounds. The gate-list length obeys the
displayed padding budget, and evaluation agrees on every encoded input state. -/
def QtmCellPhi3Compilation : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
    (b t k : ℕ) (e : CellState Q A → Reg b)
    (G : Matrix (GWindow Q A) (GWindow Q A) ℂ),
    Function.Injective e → G ∈ Matrix.unitaryGroup (GWindow Q A) ℂ →
    ∃ gs : List (Phi3Gate ((2*t+1)*b+3)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧
      gs.length ≤ k*((2*t-1)*phi3PaddingBudget (3*b)+(2*t+1)*phi3PaddingBudget b) ∧
      ∀ ψ : QState (WReg t Q A),
        Run (1 : Matrix (Reg ((2*t+1)*b+3)) (Reg ((2*t+1)*b+3)) ℂ) (phi3Compile gs)
          (qtmPhi3State t b e ψ) =
          qtmPhi3State t b e
            (Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ)
              (RepeatCircuit (kRoundCircuit t G) k) ψ)

end Qatlib.Concepts.QtmSimulation.Phi3Compilation
