/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.BoundaryRootDeflationStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial

def DeflatedSchwarzAndFilter : Prop :=
  ∀ (P : Polynomial ℂ) (d : ℕ), P.natDegree ≤ d →
    (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) →
    ∃ Q : Polynomial ℂ, BoundaryCanonical P Q d ∧
      (∀ S : Polynomial ℂ, BoundaryCanonical P S d → S = Q) ∧
      (Q ≠ 0 → ∀ z : ℂ, ‖z‖ < 1 →
        Q.eval z = boundaryComplementQuotientPhase Q*(boundaryComplementFactor Q).eval z*
          Complex.exp ((1/(4*Real.pi) : ℝ) •
            (∫ θ : ℝ in 0..2*Real.pi,
              (Complex.exp (θ*Complex.I)+z)/(Complex.exp (θ*Complex.I)-z)*
                ((Real.log (boundaryComplementProfile Q (Complex.exp (θ*Complex.I))) : ℝ) : ℂ)))) ∧
      (∀ z : ℂ, ‖z‖ = 1 →
        circleCompletion P Q z ∈ Matrix.unitaryGroup Bool ℂ ∧
        ApplyGate (circleCompletion P Q z) (Ket false) =
          (fun b : Bool => if b then Q.eval z else P.eval z))

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
