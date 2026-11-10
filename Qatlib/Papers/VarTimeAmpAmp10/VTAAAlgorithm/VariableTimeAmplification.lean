/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplificationAnswers
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmpCounterexamples
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.TightAASuccessBound
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.AmplificationProductEventBounds
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.FourierWindow
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplificationRefutations
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

private theorem householder_mem_unitary {κ : Type} [Fintype κ] [DecidableEq κ] (a : QState κ)
    (ha : Qatlib.Foundations.PureStateMath.Inner a a = 1) : (1 - (2 : ℂ) • pureDensity a) ∈ Matrix.unitaryGroup κ ℂ := by
  have hs : star (1 - (2 : ℂ) • pureDensity a) = 1 - (2 : ℂ) • pureDensity a :=
    householder_star a
  have hm : (1 - (2 : ℂ) • pureDensity a) * (1 - (2 : ℂ) • pureDensity a) = 1 :=
    householder_mul_self a ha
  have key : star (1 - (2 : ℂ) • pureDensity a) * (1 - (2 : ℂ) • pureDensity a) = 1 := by
    rw [hs]
    exact hm
  rw [Matrix.mem_unitaryGroup_iff']
  exact key

section Clause66
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
end Clause66

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
