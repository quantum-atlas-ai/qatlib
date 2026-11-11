/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.Phase
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
import Qatlib.Concepts.CoherentSim.CoherentOAA.Qubitization
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Qatlib.Concepts.OperatorErrors.Robustness
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
import Qatlib.Concepts.QspSimulation.Achievability.RealPartResponse
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.WalshMoment.Forrelation.CountedThresholdQSVT
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ThresholdOutputConsumers
import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvt
import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvtConsumers

import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.QspSimulation.WordModel.CPPAdjointDefs
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.QsvtCore.QsVtMain.QSVTConsumers
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralDefs
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralConsumer
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralDefs
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCoefficients
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCutoff
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralConsumer

import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.QspSimulation.WordModel.FinitePhaseConsumers

import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.QsvtCore.QsVtStability.SquareRootQSVTRobustness
import Qatlib.Concepts.QsvtCore.QsVtStability.RootRobustQSVTConsumers
import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ConventionBridgeConsumers

import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.FiniteFFTPolynomialMul
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2Finite

/-!
# Quantum signal processing interfaces

This module gathers the signal-processing, phase-synthesis, singular-value transformation, and
robustness interfaces used by the word model. Its imports expose constructions such as
`QSPWord`, `cppAdjointWord`, and the finite-phase consumers together with polynomial response
and convention-bridge results. Background and related constructions are discussed in
[GilyenSuLowWiebe2019].

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.QspSimulation.WordModel

open Matrix

set_option maxHeartbeats 4000000

section QSPFunctionForm

open Polynomial

end QSPFunctionForm

end Qatlib.Concepts.QspSimulation.WordModel
