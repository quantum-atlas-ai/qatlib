/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.ZeroMarginCanonicalComplementStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon

/-- Every degree bounded polynomial with unit circle modulus at most one has a boundary
canonical complement, which is zero exactly when the original modulus is identically one on
the circle. -/
theorem zeroMarginCanonicalComplement : ZeroMarginCanonicalComplement := by
  intro P d hp hb
  obtain ⟨Q, hQ⟩ := boundaryCanonical_exists P d hp hb
  exact ⟨Q, hQ, boundaryCanonical_zero_iff P Q d hQ⟩

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
