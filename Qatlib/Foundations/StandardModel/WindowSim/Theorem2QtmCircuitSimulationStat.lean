/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

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
