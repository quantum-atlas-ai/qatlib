/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c010 — Corollary 27 (product of block encodings)

Shao--Liu, arXiv:2010.15027v2, Corollary 27, p. 21.

Given `(α_i, q_i, ε_i)`-block-encodings of `A_i` obtained in time `O(T_i)`
(`i = 1,2`), the paper constructs a block encoding of `A_1 A_2` with

* scale `2 ‖A_1‖ ‖A_2‖`,
* ancillas `q_1 + q_2 + 2`,
* error `√2 (‖A_1‖ ε_2 + ‖A_2‖ ε_1)`,
* synthesis time `O(α_1 (q_1 + T_1)‖A_1‖⁻¹ + α_2 (q_2 + T_2)‖A_2‖⁻¹)`.

This module proves the numeric content of that corollary: each displayed
quantity is positive/nonnegative as claimed, the ancilla count dominates
`q_1 + q_2`, and the displayed product error dominates the two-term error
budget `‖A_1‖ ε_2 + ‖A_2‖ ε_1` that the product construction accumulates.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

/-- The product scale `2‖A₁‖‖A₂‖` is positive for nonzero operator norms. -/
theorem corollary27_scale_pos (A1norm A2norm : ℝ)
    (h1 : 0 < A1norm) (h2 : 0 < A2norm) :
    0 < productScale A1norm A2norm := by
  unfold productScale
  positivity

/-- The product error is nonnegative. -/
theorem corollary27_error_nonneg (A1norm A2norm ε1 ε2 : ℝ)
    (h1 : 0 ≤ A1norm) (h2 : 0 ≤ A2norm) (he1 : 0 ≤ ε1) (he2 : 0 ≤ ε2) :
    0 ≤ productError A1norm A2norm ε1 ε2 := by
  unfold productError
  positivity

/-- **The product error dominates the accumulated two-term budget.**  Since
`√2 ≥ 1`, the displayed error `√2(‖A_1‖ε_2 + ‖A_2‖ε_1)` is at least
`‖A_1‖ε_2 + ‖A_2‖ε_1`. -/
theorem corollary27_error_dominates
    (A1norm A2norm ε1 ε2 : ℝ)
    (h1 : 0 ≤ A1norm) (h2 : 0 ≤ A2norm) (he1 : 0 ≤ ε1) (he2 : 0 ≤ ε2) :
    A1norm * ε2 + A2norm * ε1 ≤ productError A1norm A2norm ε1 ε2 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
    rwa [Real.sqrt_one] at h
  have hsum : 0 ≤ A1norm * ε2 + A2norm * ε1 := by positivity
  unfold productError
  nlinarith

/-- The product ancilla count `q_1 + q_2 + 2` dominates the sum of the input
counts. -/
theorem corollary27_ancillas (q1 q2 : ℕ) :
    q1 + q2 ≤ productQubits q1 q2 := by
  unfold productQubits
  omega

/-- The product synthesis time is nonnegative. -/
theorem corollary27_cost_nonneg
    (α1 q1 T1 A1norm α2 q2 T2 A2norm : ℝ)
    (hα1 : 0 ≤ α1) (hq1 : 0 ≤ q1) (hT1 : 0 ≤ T1) (hA1 : 0 < A1norm)
    (hα2 : 0 ≤ α2) (hq2 : 0 ≤ q2) (hT2 : 0 ≤ T2) (hA2 : 0 < A2norm) :
    0 ≤ productCost α1 q1 T1 A1norm α2 q2 T2 A2norm := by
  unfold productCost
  positivity

end Qatlib.Papers.GenEigenODE20.MainResults
