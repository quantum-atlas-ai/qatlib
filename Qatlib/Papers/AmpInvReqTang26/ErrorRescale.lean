/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.ActualAccess

/-!
# Relative-error amplitude readout

Rewrites a strict additive error threshold `a * eps` as the interval between `(1 - eps) * a` and
`(1 + eps) * a`. The same identity rewrites the Born-weighted readout event of a preparation
algorithm without changing its mass. See [TangWright2025].

## Main statements

* `relative_error_iff`: the real inequality equivalence.
* `actual_relative_readout`: equality of the two Born-weighted readout sums.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AmpInvReqTang26.ErrorRescale
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The strict bound `|v - a| < a * eps` is equivalent to `(1 - eps) * a < v` and `v < (1 + eps)
* a`. -/
theorem relative_error_iff (a eps v : ℝ) :
    |v-a|<a*eps ↔ (1-eps)*a<v ∧ v<(1+eps)*a := by
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

/-- The Born-weighted sum for additive amplitude error below `amplitude * eps` equals the sum
for estimates strictly between `(1 - eps) * amplitude` and `(1 + eps) * amplitude`. -/
theorem actual_relative_readout {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (Alg : PreparationAlgorithm I A) (X : Matrix I I ℂ) (n : ℕ) (eps : ℝ) :
    (∑x,if |Alg.value x-preparationAmplitude Alg.start Alg.goodData X|<
      preparationAmplitude Alg.start Alg.goodData X*eps then ‖preparationRun Alg X n x‖^2 else 0) =
    ∑x,if (1-eps)*preparationAmplitude Alg.start Alg.goodData X<Alg.value x ∧
      Alg.value x<(1+eps)*preparationAmplitude Alg.start Alg.goodData X
      then ‖preparationRun Alg X n x‖^2 else 0 := by
  simp_rw [relative_error_iff]

end Qatlib.Papers.AmpInvReqTang26.ErrorRescale
