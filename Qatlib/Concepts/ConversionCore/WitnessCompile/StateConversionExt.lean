/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.StateConversion
import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan

/-!
# Analytic instances for continuous state conversion

This module imports continuous and optimized state-conversion interfaces and supplies local
analytic instances for finite complex matrix spaces. The instances make the L2 operator norm
compatible with extended norms and provide pseudometrizability for the continuous-conversion
setting.

The state-conversion background is [LeeEtAl2011].

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QueryComplexity.StateConversion
open scoped BigOperators Classical Matrix.Norms.L2Operator ENNReal ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

section SourceContinuousAnalytic
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.ModelSemantics Qatlib.Concepts.QueryComplexity.StateConversion
open MeasureTheory Set Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator Topology

local instance continuousConversion_matrixENormed (H : Type) [Fintype H] :
    ENormedAddCommMonoid (Matrix H H ℂ) :=
  @NormedAddCommGroup.toENormedAddCommMonoid _ Matrix.instL2OpNormedAddCommGroup

local instance continuousConversion_matrixPseudoMetrizable (H : Type) [Fintype H] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix H H ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (H → H → ℂ)
  infer_instance

end SourceContinuousAnalytic

end Qatlib.Concepts.ConversionCore.WitnessCompile
