/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.MetricLossEquivalenceStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def Corollary31MetricBounds : Prop :=
  ∀ (P Q Q' : Polynomial ℂ) (d : ℕ) (ε : ℝ),
    P.natDegree ≤ d → Q.natDegree ≤ d → Q'.natDegree ≤ d →
    0 < ε → ε < 1 →
    (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2 + ‖Q.eval z‖^2 = 1) →
    (∀ n : ℕ, n ≤ d → ‖Q.coeff n - Q'.coeff n‖ < ε) →
    sourcePhiUniform P Q' < ((d : ℝ) + 1) * ((d : ℝ) + 3) * ε ∧
    sourcePhiTilde P Q' d < 3 * ((d : ℝ) + 1) * (2 * (d : ℝ) + 1) * ε

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
