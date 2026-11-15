/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.MetricLossEquivalenceComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Corollary31MetricBoundsComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Theorem3CorrectedCoefficientsComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Theorem4CorrectedComplementarityComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Algorithm1CoefficientProgramComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Alg1CoefficientProgramCorrectedComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Algorithm2TotalCostEndpointComp
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.DeflatedFourierRootFactorFormComp

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
example : MetricLossEquivalence := metricLossEquivalence
example : Corollary31MetricBounds := corollary31MetricBounds
example : Theorem3CorrectedCoefficients := theorem3CorrectedCoefficients
example : Theorem4CorrectedComplementarity := theorem4CorrectedComplementarity
example : Algorithm1CoefficientProgram := algorithm1CoefficientProgram
example : Algorithm1CoefficientProgramCorrected := algorithm1CoefficientProgramCorrected
example : Algorithm2TotalCostEndpoint := algorithm2TotalCostEndpoint
example : DeflatedFourierRootFactorForm := deflatedFourierRootFactorForm

/-- Collects the loss equivalence, coefficient accuracy, complementarity, algorithm cost, and
deflated Fourier factorization results for complementary polynomials. -/
theorem complementary_polynomials_residual_consumers :
    MetricLossEquivalence ∧
    Corollary31MetricBounds ∧
    Theorem3CorrectedCoefficients ∧
    Theorem4CorrectedComplementarity ∧
    Algorithm1CoefficientProgram ∧
    Algorithm1CoefficientProgramCorrected ∧
    Algorithm2TotalCostEndpoint ∧
    DeflatedFourierRootFactorForm :=
  ⟨metricLossEquivalence,
   corollary31MetricBounds,
   theorem3CorrectedCoefficients,
   theorem4CorrectedComplementarity,
   algorithm1CoefficientProgram,
   algorithm1CoefficientProgramCorrected,
   algorithm2TotalCostEndpoint,
   deflatedFourierRootFactorForm⟩
end Qatlib.Concepts.LaurentPolys.BoundaryCanon
