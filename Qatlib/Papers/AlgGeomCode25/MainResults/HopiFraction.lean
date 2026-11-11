/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! HOPI satisfaction-fraction lemmas for
"Algebraic Geometry Codes and Decoded Quantum Interferometry"
(arXiv:2510.06603v1, 2025).

Theorem 1 of the paper states that Decoded Quantum Interferometry on a
HOPI instance over the Hermitian curve achieves an expected satisfaction
fraction `⟨s⟩/n = (√((l/n)(1 − r/q²)) + √((r/q²)(1 − l/n)))²` in the
regime `r/q² ≤ 1 − l/n` (and `1` otherwise), where `n = q³`, `r` is the
constraint-set size and `l` the decoding radius. The paper derives this
by reduction to the semicircle law of the DQI reference, without an
in-paper proof.

- `satisfaction_fraction_le_one` proves the arithmetic core of that
  formula: for all `x, y ∈ [0, 1]` (no branch condition needed), the
  squared-hellinger expression stays at most `1`, i.e. the predicted
  satisfaction fraction is a well-defined fraction for every parameter
  regime. The proof identifies the cross term with an AM–GM product
  `(1−x)(1−y)·xy` whose mean dominates `2√·`.

No axiom, no `admit`, no `native_decide`. -/
set_option autoImplicit false

namespace Qatlib.Papers.AlgGeomCode25.MainResults.HopiFraction

/-- **Theorem 1, arithmetic core**: for all `x, y ∈ [0, 1]`, the
satisfaction-fraction expression
`(√(x(1−y)) + √(y(1−x)))²` is at most `1`. Instantiating `x = l/n`
and `y = r/q²` gives that the DQI satisfaction fraction predicted by
Theorem 1 is a genuine fraction in every parameter regime (the paper's
branch `r/q² ≤ 1 − l/n` is only needed to decide whether the value is
`< 1` or identically `1`). -/
theorem satisfaction_fraction_le_one (x y : ℝ)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    (Real.sqrt (x * (1 - y)) + Real.sqrt (y * (1 - x))) ^ 2 ≤ 1 := by
  have hxy : 0 ≤ x * (1 - y) := mul_nonneg hx (sub_nonneg.mpr hy')
  have hyx : 0 ≤ y * (1 - x) := mul_nonneg hy (sub_nonneg.mpr hx')
  have hw : 0 ≤ (1 - x) * (1 - y) := mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy')
  have hz : 0 ≤ x * y := mul_nonneg hx hy
  have hprod : x * (1 - y) * (y * (1 - x)) = (1 - x) * (1 - y) * (x * y) := by ring
  have hsum : x * (1 - y) + y * (1 - x) = 1 - ((1 - x) * (1 - y) + x * y) := by ring
  have hamgm : 2 * Real.sqrt ((1 - x) * (1 - y) * (x * y))
      ≤ (1 - x) * (1 - y) + x * y := by
    have h1 : 0 ≤ 2 * Real.sqrt ((1 - x) * (1 - y) * (x * y)) := by positivity
    have h2 : 0 ≤ (1 - x) * (1 - y) + x * y := add_nonneg hw hz
    have hsq : (2 * Real.sqrt ((1 - x) * (1 - y) * (x * y))) ^ 2
        ≤ ((1 - x) * (1 - y) + x * y) ^ 2 := by
      have key : (2 * Real.sqrt ((1 - x) * (1 - y) * (x * y))) ^ 2
          + ((1 - x) * (1 - y) - x * y) ^ 2
          = ((1 - x) * (1 - y) + x * y) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hw hz), sub_sq, add_sq]
        ring
      linarith [key, sq_nonneg ((1 - x) * (1 - y) - x * y)]
    have habs := (sq_le_sq).mp hsq
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at habs
  rw [add_sq, Real.sq_sqrt hxy, Real.sq_sqrt hyx, mul_assoc,
    ← Real.sqrt_mul hxy (y * (1 - x)), hprod]
  linarith

end Qatlib.Papers.AlgGeomCode25.MainResults.HopiFraction
