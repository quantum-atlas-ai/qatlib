/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs

/-!
# Completeness and positivity of square root effects

Defines `squareRootEffect` by sandwiching an outer product between two copies of a matrix `W`.
For Hermitian `W`, a decomposition of `G` into the given outer products and the identity `W * G
* W = 1` ensure that these effects sum to the identity and are positive semidefinite.

This algebraic criterion supports the square root measurement construction in quantum template
matching [SasakiCarliniJozsa2001].

## Main statements

* `squareRootMeasurement_isPOVM`: proves completeness and positivity of the constructed effects.

## References

* [Sasaki et al., 2001][SasakiCarliniJozsa2001]
-/

set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate

open Qatlib.Foundations.PureStateMath
open Matrix BigOperators
open scoped ComplexOrder MatrixOrder Matrix

set_option autoImplicit false

variable {d M : ℕ}

/-- The effect `W * |v⟩⟨v| * W` formed from a vector `v` and a matrix `W`. -/
noncomputable def squareRootEffect (W : Operator d) (v : Fin d → ℂ) : Operator d :=
  W * Matrix.vecMulVec v (star v) * W

/-- If `W` is Hermitian, `G` is the sum of the given vector outer products, and `W * G * W = 1`,
then the corresponding square root effects sum to the identity and are positive
semidefinite. See [SasakiCarliniJozsa2001]. -/
theorem squareRootMeasurement_isPOVM
    (W G : Operator d) (v : Fin M → Fin d → ℂ) (hW : Wᴴ = W)
    (hG : G = ∑ m, Matrix.vecMulVec (v m) (star (v m)))
    (hWG : W * G * W = 1) :
    (∑ m, squareRootEffect W (v m)) = 1 ∧
      ∀ m, (squareRootEffect W (v m)).PosSemidef := by
  constructor
  · have hsum : (∑ m, squareRootEffect W (v m))
        = W * (∑ m, Matrix.vecMulVec (v m) (star (v m))) * W := by
      simp only [squareRootEffect]
      rw [Matrix.mul_sum, Matrix.sum_mul]
    rw [hsum, ← hG, hWG]
  · intro m
    have hP : (Matrix.vecMulVec (v m) (star (v m))).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star _
    have h := hP.mul_mul_conjTranspose_same W
    simpa [squareRootEffect, hW] using h

end Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate
