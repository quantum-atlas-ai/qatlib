/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GramQueryCore.ModelSemantics.AlphabetWordSemanticsQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormBasicLawsQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.DualNormSDPAndClosureQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.PhaseDetectionQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetWitnessGeometryQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessSpectralMassesQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
public import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan
public import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedReturnedWordConsumersQuan
public import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
public import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.QueryDirectSumConsumerQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.NativeCodeSemanticsQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.ActualNativeNonzeroQueryConsumerQuan

@[expose] public section

/-!
# Consumer checks for witness-conversion interfaces

This module checks that the imported results inhabit the residual specification predicates for
filtered norms, spectral geometry, adaptive purification, and concrete query semantics. Its
anonymous examples include `WitnessSpectralMasses`, `RealBudgetConversionAlgorithm`, and
`ActualNativeNonzeroQueryConsumer`.

These checks assemble interfaces for the filtered state-conversion framework of [LeeEtAl2011]
and reflection algorithms of [Reichardt2011].

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QueryComplexity.StateConversion

namespace Qatlib.Concepts.ConversionCore.WitnessCompile

example : AlphabetWordSemantics := Qatlib.Concepts.GramQueryCore.ModelSemantics.alphabetWordSemantics
example : RectangularBudgetRealization := Qatlib.Concepts.GramQueryCore.FilteredNorm.rectangularBudgetRealization
example : RectangularSchurDuality := Qatlib.Concepts.GramQueryCore.FilteredNorm.rectangularSchurDuality
example : FilteredNormBasicLaws := Qatlib.Concepts.GramQueryCore.FilteredNorm.filteredNormBasicLaws
example : FilteredNormClosureLaws := Qatlib.Concepts.GramQueryCore.FilteredNorm.filteredNormClosureLaws
example : FilteredNormCompositionAndProducts := Qatlib.Concepts.GramQueryCore.FilteredNorm.filteredNormCompositionAndProducts
example : DualNormSDPAndClosure := Qatlib.Concepts.GramQueryCore.FilteredNorm.dualNormSDPAndClosure
example : FunctionEvaluationNormSandwich := Qatlib.Concepts.GramQueryCore.FilteredNorm.functionEvaluationNormSandwich
example : EffectiveSpectralGap := Qatlib.Concepts.ConversionCore.WitnessCompile.effectiveSpectralGap
example : PhaseDetection := Qatlib.Concepts.GramQueryCore.LowerBoundTools.phaseDetection
example : AlphabetWitnessGeometry := Qatlib.Concepts.GramQueryCore.LowerBoundTools.alphabetWitnessGeometry
example : WitnessSpectralMasses := Qatlib.Concepts.ConversionCore.WitnessCompile.witnessSpectralMasses
example : AlphabetPhaseWordAssembly := Qatlib.Concepts.GramQueryCore.LowerBoundTools.alphabetPhaseWordAssembly
example : GeneralOutputGramBridges := Qatlib.Concepts.GramQueryCore.LowerBoundTools.generalOutputGramBridges
example : RealBudgetConversionAlgorithm := Qatlib.Concepts.QueryComplexity.StateConversion.realBudgetConversionAlgorithm
example : OptimizedReturnedWordConsumers := Qatlib.Concepts.QueryComplexity.StateConversion.optimizedReturnedWordConsumers
example : OptimizedConversionEndpoints := Qatlib.Concepts.QueryComplexity.StateConversion.optimizedConversionEndpoints
example : BooleanValueCompatibility := Qatlib.Concepts.GramQueryCore.ModelSemantics.booleanValueCompatibility
example : FunctionEvaluationAdversaryAlgorithm := Qatlib.Concepts.ConversionCore.WitnessCompile.functionEvaluationAdversaryAlgorithm
example : VolterraAndOracleLogSemantics := Qatlib.Concepts.GramQueryCore.ModelSemantics.volterraAndOracleLogSemantics
example : AdaptiveInstrumentPurification := Qatlib.Concepts.ConversionCore.WitnessCompile.adaptiveInstrumentPurification
example : FunctionCompositionBounds := Qatlib.Concepts.GramQueryCore.GammaDuality.functionCompositionBounds
example : QueryDirectSumConsumer := Qatlib.Concepts.ConversionCore.WitnessCompile.queryDirectSumConsumer
example : NativeCodeSemantics := Qatlib.Concepts.GramQueryCore.ModelSemantics.nativeCodeSemantics
example : ActualNativeNonzeroQueryConsumer := Qatlib.Concepts.ConversionCore.WitnessCompile.actualNativeNonzeroQueryConsumer

end Qatlib.Concepts.ConversionCore.WitnessCompile
