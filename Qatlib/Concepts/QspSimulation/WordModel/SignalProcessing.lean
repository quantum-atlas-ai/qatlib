/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.PhaseGeometry.Phase
public import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Qubitization
public import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
public import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
public import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
public import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
public import Qatlib.Concepts.OperatorErrors.Robustness
public import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
public import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
public import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
public import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
public import Qatlib.Concepts.QspSimulation.Achievability.RealPartResponse
public import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
public import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Concepts.WalshMoment.Forrelation.CountedThresholdQSVT
public import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ThresholdOutputConsumers
public import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvt
public import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvtConsumers

public import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
public import Qatlib.Concepts.QspSimulation.WordModel.CPPAdjointDefs
public import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
public import Qatlib.Concepts.QsvtCore.QsVtMain.QSVTConsumers
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralDefs
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralConsumer
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralDefs
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCoefficients
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCutoff
public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralConsumer

public import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData
public import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid
public import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
public import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
public import Qatlib.Concepts.QspSimulation.WordModel.FinitePhaseConsumers

public import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
public import Qatlib.Concepts.QsvtCore.QsVtStability.SquareRootQSVTRobustness
public import Qatlib.Concepts.QsvtCore.QsVtStability.RootRobustQSVTConsumers
public import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt

public import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
public import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.ConventionBridgeConsumers

public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2
public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.FiniteFFTPolynomialMul
public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2Finite

@[expose] public section

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
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.QspSimulation.WordModel

open Matrix

set_option maxHeartbeats 4000000

section QSPFunctionForm

open Polynomial

end QSPFunctionForm

end Qatlib.Concepts.QspSimulation.WordModel
