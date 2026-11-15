/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.BoundaryCanonicalComplement
public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def Algorithm2TotalCostEndpoint : Prop :=
  ∀ (P₀ : Polynomial ℂ) (d : ℕ) (ε : ℝ), 0 < d → P₀.natDegree ≤ d →
    0 < ε → ε < 1 → (∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1) →
    ∃ (m : ℕ) (Q : Polynomial ℂ),
      1 ≤ m ∧ d+1 ≤ 2^m ∧
      ((2^m : ℕ) : ℝ) ≤ 512*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε)) ∧
      Q = canonicalComplementFourierPolynomial (((1-ε/4 : ℝ) : ℂ) • P₀) d m ∧
      Q.natDegree ≤ d ∧
      (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q z < ε) ∧
      (∀ z : ℂ, ‖z‖ = 1 →
        ‖(circleCompletion P₀ Q z)ᴴ * circleCompletion P₀ Q z - 1‖ < ε) ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications ≤
        32768*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε))^2 ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).additions ≤
        32768*((d : ℝ)/ε)*(1+Real.log ((d : ℝ)/ε))^2 ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).logarithms = 2^m ∧
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).exponentials = 2^m

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
