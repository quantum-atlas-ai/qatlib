/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.BoundaryCanonicalComplement

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Qatlib

def ZeroMarginCanonicalComplement : Prop :=
  ∀ (P : Polynomial ℂ) (d : ℕ), P.natDegree ≤ d →
    (∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) →
    ∃ Q : Polynomial ℂ, BoundaryCanonical P Q d ∧
      (Q = 0 ↔ ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ = 1)

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
