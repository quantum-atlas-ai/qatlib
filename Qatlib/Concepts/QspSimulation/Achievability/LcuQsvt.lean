/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedLowc
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# QSP simulation and phase synthesis imports

This module collects imports for polynomial phase synthesis, restricted QSP compilation,
Jacobi–Anger degree bounds, and sparse Hamiltonian simulation. It provides a common import
surface for the QSP framework of [LowChuang2017] and the polynomial transformation framework of
[GilyenSuLowWiebe2019].

## Main statements

* `QspCompilationRestricted`: The imported scalar compilation guarantee for restricted QSP
  responses.
* `JacobiAngerCorrectedDegree`: The imported specification of the corrected truncation degree.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.SparseSim
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Polynomial
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib.Concepts.QspSimulation.SparseWalk Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SignalPrimitive.SparseSim

end Qatlib.Concepts.QspSimulation.Achievability
