/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCoordinateTruncation
public import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

@[expose] public section


/-!
# Rational root-coordinate decoder bridge

Retains the decoder equality of the original root-completion development; the
remaining declarations of that development are already provided by the fixed
public library.
-/

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The rational root coordinate decodes to the complex number with the same rational components. -/
theorem rootCompletion_decode_existing (u : ℚ × ℚ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.rootRationalCoordinate u =
      Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase.gaussianRatComplex u := by
  apply Complex.ext <;>
    simp [Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.rootRationalCoordinate,
      Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase.gaussianRatComplex]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
