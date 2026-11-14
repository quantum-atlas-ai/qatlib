/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ConversionCore.WitnessCompile.QueryDirectSumConsumerQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan
public import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.ActualNativeNonzeroQueryConsumerQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessSpectralMassesQuan
public import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetWitnessGeometryQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.DualNormSDPAndClosureQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.NativeCodeSemanticsQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.PhaseDetectionQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormBasicLawsQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityQuan
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.AlphabetWordSemanticsQuan
public import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
public import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
public import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
public import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedReturnedWordConsumersQuan
public import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan
public import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
public import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionResidualConsumers

@[expose] public section

/-!
# Entry point for witness-conversion results

This module collects the filtered-norm, witness-geometry, and query-program results used by
state-conversion consumers. It imports `WitnessSpectralMasses`, adaptive purification,
native-code semantics, and the residual consumer checks without introducing new named
mathematical declarations.

The imported interfaces connect filtered Gram certificates to query algorithms in the setting of
[LeeEtAl2011] and reflection constructions of [Reichardt2011].

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
