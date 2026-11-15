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
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def profileLogCoeff (Q : Polynomial ℂ) (n : ℕ) : ℂ :=
  (2*Real.pi*Complex.I)⁻¹ *
    (∮ z : ℂ in C(0,1),
      z^(-((n+1 : ℕ) : ℤ)) * (Real.log (boundaryComplementProfile Q z) : ℂ))

def profileLogSeries (Q : Polynomial ℂ) (z : ℂ) : ℂ :=
  (∑' n : ℕ, profileLogCoeff Q n * z^n) - profileLogCoeff Q 0 / 2

def DeflatedFourierRootFactorForm : Prop :=
  ∀ (P Q : Polynomial ℂ) (d : ℕ), BoundaryCanonical P Q d → Q ≠ 0 →
    let Q₀ := boundaryComplementFactor Q
    let ζ := boundaryComplementQuotientPhase Q
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      Q.eval z = ζ * Q₀.eval z * Complex.exp (profileLogSeries Q z)

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
