/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.Theorem2QtmCircuitSimulationQuan
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Theorem2Simulation

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile

theorem theorem2_qtm_circuit_simulation : Theorem2QtmCircuitSimulation :=
  theorem2QtmCircuitSimulation

theorem theorem2_phi3_elementary_compilation : QtmPhi3WindowSimulation :=
  qtmPhi3WindowSimulation

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Theorem2Simulation
