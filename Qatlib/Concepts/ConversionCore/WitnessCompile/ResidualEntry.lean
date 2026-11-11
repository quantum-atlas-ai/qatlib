/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.QueryDirectSumConsumerQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.ActualNativeNonzeroQueryConsumerQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessSpectralMassesQuan
import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetWitnessGeometryQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.DualNormSDPAndClosureQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.NativeCodeSemanticsQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.PhaseDetectionQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormBasicLawsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.AlphabetWordSemanticsQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedReturnedWordConsumersQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionResidualConsumers

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
set_option warningAsError false
