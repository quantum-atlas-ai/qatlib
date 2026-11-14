/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
public import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
public import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
public import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
public import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
public import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
public import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
public import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplificationAnswers
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmpCounterexamples
public import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.TightAASuccessBound
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.AmplificationProductEventBounds
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.FourierWindow
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplificationRefutations

@[expose] public section

/-!
# Unitarity of the Householder reflection

This module proves that the Householder matrix formed from a unit vector is unitary. The result
supports the unitary state transformations used in the surrounding variable-time amplification
development.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `householder_mem_unitary`: unitarity of `1 - 2 • pureDensity a` for a unit vector.

## References

* [Ambainis, 2012][Ambainis2012]
-/

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

/-- For a state with inner product one with itself, the Householder matrix `1 - 2 • pureDensity
a` is unitary. -/
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
