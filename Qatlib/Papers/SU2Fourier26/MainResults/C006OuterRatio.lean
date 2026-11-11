/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceBeurlingWeight

/-!
# Lemma 2: `(a, b) ∈ A_w` with `‖b‖_∞ < 1` iff `b/a* ∈ A_w` (c006)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Lemma 2, p.8.

Let `w` be a strong Beurling weight, `a` outer on `𝔻*` and `|a|² + |b|² = 1`.
Then `a, b ∈ A_w` with `‖b‖_{L∞(𝕋)} < 1` is equivalent to `b/a* ∈ A_w`.

The paper's proof (p.8): `(a) ⇒ (b)` uses that `1/a* ∈ A_w` (Wiener's lemma,
Lemma 1) and closure of `A_w` under pointwise products; `(b) ⇒ (a)` runs the
argument backwards through functional calculus (`log`, `exp`, Hilbert transform).

Here we formalize the preliminary point that makes the quotient `b/a*` — and the
paper's normalization `‖b‖_{L∞} < 1` — meaningful: the SU(2) constraint
`|a|² + |b|² = 1` together with `‖b‖_{L∞} < 1` forces `a` to be everywhere
nonzero.  The product-closure and functional-calculus parts of Lemma 2 are
*not* formalized.

The full statement is recorded for reference:

```
theorem outer_iff_ratio_memAW (W : StrongBeurlingWeight) (a b : CircleT → ℂ)
    (hout : IsOuterInDStar W a)
    (hunit : ∀ x : CircleT, a x * starFun a x + b x * starFun b x = 1) :
    (MemAW W a ∧ MemAW W b ∧ MemBallLinfty b) ↔
      MemAW W (fun x => b x / starFun a x)
```
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- The denominator in Lemma 2 of arXiv:2603.02021v1, p.8, never vanishes: under
the SU(2) normalization `a·a* + b·b* = 1` (1.2) and the strict bound
`‖b‖_{L∞(𝕋)} < 1`, one has `a x ≠ 0` for every `x : 𝕋`.  This is what makes the
quotient `b/a*` (and its membership in `A_w`) well posed. -/
theorem a_ne_zero_of_unit {a b : CircleT → ℂ}
    (hunit : ∀ x : CircleT, a x * starFun a x + b x * starFun b x = 1)
    (hb : ∀ x : CircleT, ‖b x‖ < 1) (x : CircleT) : a x ≠ 0 := by
  intro ha
  have hbx : b x * starFun b x = 1 := by
    have h := hunit x
    rw [ha, zero_mul, zero_add] at h
    exact h
  have hnorm : ‖b x‖ * ‖starFun b x‖ = 1 := by
    rw [← norm_mul, hbx, norm_one]
  have h1 : ‖b x‖ < 1 := hb x
  have h2 : ‖starFun b x‖ < 1 := by simpa [starFun] using hb (-x)
  have h3 : ‖b x‖ * ‖starFun b x‖ < 1 := by
    rcases eq_or_lt_of_le (norm_nonneg (starFun b x)) with hy | hy
    · rw [← hy, mul_zero]; exact zero_lt_one
    · calc ‖b x‖ * ‖starFun b x‖ < 1 * ‖starFun b x‖ :=
            mul_lt_mul_of_pos_right h1 hy
        _ < 1 * 1 := mul_lt_mul_of_pos_left h2 zero_lt_one
        _ = 1 := one_mul 1
  linarith

end

end Qatlib.Papers.SU2Fourier26.MainResults
