/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.Theorem2QtmCircuitSimulationQuan
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationQuan

/-!
# QTM circuit simulation endpoints

The module exposes the finite-window QTM simulation property `Theorem2QtmCircuitSimulation` and
the elementary compilation property `QtmPhi3WindowSimulation`. These endpoints connect the
window simulation with its circuit and elementary-gate formulations. See [Yao1993].

## Main statements

* `theorem2_qtm_circuit_simulation`: establishes the QTM circuit simulation contract.
* `theorem2_phi3_elementary_compilation`: establishes the elementary-gate window simulation
  contract.

## References

* [Yao, 1993][Yao1993]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Theorem2Simulation

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile

/-- The finite-window circuit simulation property `Theorem2QtmCircuitSimulation` holds, giving
the circuit simulation endpoint associated with Theorem 2 of [Yao1993]. -/
theorem theorem2_qtm_circuit_simulation : Theorem2QtmCircuitSimulation :=
  theorem2QtmCircuitSimulation

/-- The elementary-gate window simulation property `QtmPhi3WindowSimulation` holds. This gives
the elementary compilation endpoint associated with Theorem 2 of [Yao1993]. -/
theorem theorem2_phi3_elementary_compilation : QtmPhi3WindowSimulation :=
  qtmPhi3WindowSimulation

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Theorem2Simulation
