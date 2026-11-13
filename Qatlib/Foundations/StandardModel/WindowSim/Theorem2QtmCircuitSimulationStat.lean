/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs

/-!
# Quantum Turing machine circuit simulation contract

`Theorem2QtmCircuitSimulation` specifies a unitary circuit simulation of `t` finite-window
machine steps for positive input length `n ≤ t`. It requires zero oracle queries, at most `2 * t
* t` gates, equality of embedded output states, and equality of Born probabilities on encoded
configurations.

The mathematical background is discussed in [Yao1993].

## Main statements

* `Theorem2QtmCircuitSimulation`: the circuit existence, cost, state equality, and probability
  equality specification.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

/-- The proposition that every local quantum Turing machine has, for positive `n ≤ t`, a unitary
circuit using no queries and at most `2 * t * t` gates that reproduces `t` window steps and
their encoded Born probabilities on initialized inputs. -/
def Theorem2QtmCircuitSimulation : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
      (M : LocalQTM Q A) (n t : ℕ), 0 < n → 0 < t → n ≤ t →
    ∃ C : Circuit (WReg t Q A),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧ GateCount C ≤ 2 * t * t ∧
        ∀ x : Fin n → A, ∀ c : WindowCfg t Q A,
          Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) C
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x)))
            = windowEmbed ((windowStep M) ^ t *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M n x)) ∧
          BornProb (Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) C
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x)))) (windowEncode c)
            = BornProb ((windowStep M) ^ t *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M n x)) c

end Qatlib.Foundations.StandardDefs.WindowSim
