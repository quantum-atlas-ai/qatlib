/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs

/-!
# One-round window simulation contract

`OneRoundWindowSimulation` states that one local gate sweep and marker swap reproduces the
embedded transition of a quantum Turing machine on every encoded configuration with an interior
head. Its hypotheses specify the fixed local states and the required action on head basis
states.

The mathematical background is discussed in [Yao1993].

## Main statements

* `OneRoundWindowSimulation`: the equality between one circuit round and one embedded machine
  step.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

/-- The proposition that every gate satisfying `GUnitFixesH` and `GUnitSteps` implements one
machine step on each encoded configuration with an interior head. -/
def OneRoundWindowSimulation : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
      (M : LocalQTM Q A) (t : ℕ), 0 < t →
    ∀ G : Matrix (GWindow Q A) (GWindow Q A) ℂ,
      GUnitFixesH M G → GUnitSteps M G →
        ∀ c : WindowCfg t Q A,
          0 < c.head.val → c.head.val < 2 * t →
            Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
                (Qatlib.Foundations.PureStateMath.Ket (windowEncode c))
              = windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c)

end Qatlib.Foundations.StandardDefs.WindowSim
