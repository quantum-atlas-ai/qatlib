/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3CharacterizationGily
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23PolynomialLevel
import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseGily
import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41OriginalPseudoinverseGily
import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41WindowedPolynomialGily
import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostBoundsGily
import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostEquationGily
import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma25SignApproximationGily
import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma29RectangleApproximationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma9ChebyshevWordGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionQSVTGeneralGily
import Qatlib.Papers.QSingValue19.AlgorithmApps.LcuQsvt
import Qatlib.Concepts.QspSimulation.Achievability.SimQsp
import Qatlib.Concepts.QspSimulation.Achievability.SimQspDefs
import Qatlib.Concepts.SignalPrimitive.SparseSim.Lc17AuxWalkBranch
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWord
import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41ClosedGapConsumer

/-!
# QSVT linear systems resource definitions

This module defines the access ledger, scalar degree budget, corrected window count, and program
resource record used in the linear systems implementation associated with
[GilyenSuLowWiebe2019]. The constructor `qlsQsvtProgramBudget` transfers qubit, time, and gate
values from a gate level simulation.

## Main statements

* `nearOptimalDegreeBudget`: Takes the natural ceiling of κ² log(1/ε).
* `qlsQsvtProgramBudget`: Records simulation resources and a supplied classical bit count.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.HamiltonianSim
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.QsVtMain

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.Implementation

open Qatlib
open Matrix

/-- The QSVT access ledger using source compilation counts at degree d and supplied integer time
and peak workspace values. -/
def qlsQsvtAccessLedger (d : ℕ) (bitTime peakWorkspace : ℕ) : QsvtCostLedger where
  dataQueries := (sourceCppQuadruple d).1
  adjointQueries := (sourceCppQuadruple d).1
  projectorNots := (sourceCppQuadruple d).2.1
  phaseGates := (sourceCppQuadruple d).2.2.2
  elementaryGates := 0
  integerBitTime := bitTime
  peakWorkspace := peakWorkspace

/-- The natural ceiling of the scalar degree expression κ² log(1/ε). -/
noncomputable def nearOptimalDegreeBudget (κ : ℝ) (ε : ℝ) : ℕ :=
  Nat.ceil (κ ^ 2 * Real.log (1 / ε))

/-- The corrected window count `lcCorrectedQ` τ ε. -/
noncomputable def nearOptimalWindowCount (τ ε : ℝ) : ℕ := lcCorrectedQ τ ε

/-- A record of qubit count, classical bit count, bit time, and gate count. -/
structure QlsQsvtProgramBudget where

  qubits : ℕ

  classicalBits : ℕ

  bitTime : ℕ

  gateCount : ℕ

/-- Forms a program budget from a gate level simulation and a supplied classical bit count. -/
def qlsQsvtProgramBudget (P : GateLevelSimulation) (classicalBits : ℕ) :
    QlsQsvtProgramBudget where
  qubits := P.qubitCount
  classicalBits := classicalBits
  bitTime := P.bitTime
  gateCount := baseGateCost P

end Qatlib.Papers.QSingValue19.Implementation
