/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceCoefficientOps
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lemma 6: the normalized ratio bound (c010)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Lemma 6, (3.12)–(3.13), p.12–13.

If `‖b‖_{A_w} < 1`, then `‖Ã*ₙ/Ã*‖_{A_w} ≤ 1/(1 − ‖b‖²_{A_w})`.

The paper's proof (p.13) applies the resolvent equation (3.6) to `y = (1,0)ᵀ`,
projects onto `P₊` using the triangularity `P₋ U P₊ = 0` and `P₊ L⁻¹ u = 0`
(Lemma 3), and obtains the fixed-point identity

`Ã*ₙ/Ã* = 1 + P₊(b* P_{>n}((b/a*) Ã*ₙ/Ã*))`,

whence `‖Ã*ₙ/Ã*‖_{A_w} ≤ 1 + ‖b‖²_{A_w} ‖Ã*ₙ/Ã*‖_{A_w}` and the stated
`1/(1 − ‖b‖²_{A_w})`.

Here we formalize the scalar fixed-point inequality that concludes this argument
(and is reused verbatim in Proposition 2).  The projection algebra and the
submultiplicativity of `‖·‖_{A_w}` that produce the inequality as input are not
formalized.

The full statement is recorded for reference:

```
theorem normalized_ratio_norm_bound (W : StrongBeurlingWeight) (a b An Bn : CircleT → ℂ)
    (n : ℤ) (h : OuterSetup W a b) (hb : AWnorm W b < 1)
    (hsolve : IsNormalizedRenorm W a b n An Bn) :
    AWnorm W (fun x => starFun An x / starFun a x) ≤ 1 / (1 - AWnorm W b ^ 2)
```
-/

open scoped BigOperators Matrix
open Matrix MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- The scalar fixed-point inequality closing the proof of Lemma 6
(arXiv:2603.02021v1, p.13, (3.13)): a nonnegative quantity `x` with `x ≤ 1 + r x`
and `r < 1` is bounded by `1/(1 - r)`.  In the paper `x = ‖Ã*ₙ/Ã*‖_{A_w}` and
`r = ‖b‖²_{A_w}`. -/
theorem scalar_fixed_point_bound {x r : ℝ} (hr1 : r < 1) (h : x ≤ 1 + r * x) :
    x ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

/-- The `a*(0)` normalization step of Lemma 6 (arXiv:2603.02021v1, p.13): under
the outer-function normalization `0 < a*(0)`, dividing by it preserves the
`1/(1 - ‖b‖²)` bound.  This records the paper's final step from (3.13) to the
stated conclusion via `0 < a*(0) ≤ a*ₙ(0)`. -/
theorem ratio_bound_of_fixed_point {X r a0 : ℝ} (ha0 : 0 < a0) (hr : r < 1)
    (h : X ≤ 1 / (1 - r)) : X * a0 ≤ a0 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  calc X * a0 ≤ (1 / (1 - r)) * a0 := by
        exact mul_le_mul_of_nonneg_right h (le_of_lt ha0)
    _ = a0 / (1 - r) := by ring

end

end Qatlib.Papers.SU2Fourier26.MainResults
