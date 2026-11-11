/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerHorner
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCommonDenominator

set_option backward.isDefEq.respectTransparency false

/-! Consume the actual LCM center and the complete compact source recurrence
in one statement. No external decoded-point identity or denominator premise. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open scoped BigOperators

/-- Same original rational center and all original ascending coefficients. -/
theorem rootSharedCompactHorner_correct (n : ℕ) (a : Fin (n+1) → ℤ) (c : ℚ×ℚ) :
    gaussianPointValue (rootCompactHorner (rootSharedNumerator c)
      (rootSharedDenominator c) (List.ofFn a))=
        ∑ i : Fin (n+1),gaussianScalarDecode 0 (a i,0)*(rootRationalCoordinate c)^i.val := by
  have h := rootCompactHorner_correct n a (rootSharedNumerator c)
    (rootSharedDenominator c) (rootSharedDenominator_pos c)
  simpa only [rootSharedPoint_value] using h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
