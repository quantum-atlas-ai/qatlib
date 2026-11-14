/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
public import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
public import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
public import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
public import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
public import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
public import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
public import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
public import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
public import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
public import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedLowc
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

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
