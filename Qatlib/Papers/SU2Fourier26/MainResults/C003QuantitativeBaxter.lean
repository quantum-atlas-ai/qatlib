/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceNLFTModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 2: quantitative Baxter estimate (c003)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Proposition 2 and (1.5), p.3.

If `a*` is outer in `𝔻`, `w` is a strong Beurling weight and
`‖b‖_{A_w} < 1/√2 − ε`, then `‖F‖_{ℓ¹_w} ≲ ε^{-1} ‖b/a‖_{A_w}`.

The paper's proof (p.3) combines Lemma 6 (the `1/(1 − ‖b‖²)` bound on the
normalized ratio) with the geometric expansion of `F` in powers of `b/a` inside
the Banach algebra `A_w`; the hypothesis `‖b‖_{A_w} < 1/√2 − ε` makes every
constant uniform in the truncation index once `‖b‖² < 1`.

Here we formalize the arithmetic core of that hypothesis: the threshold
`1/√2` is strictly below `1`, hence the Proposition 2 hypothesis with `ε > 0`
implies the strict smallness `‖b‖_{A_w} < 1` required by Lemmas 4–6.  The
Banach-algebra geometric expansion and the `ℓ¹_w` bound itself are *not*
formalized.

The full statement is recorded for reference:

```
theorem quantitative_baxter_bound (W : StrongBeurlingWeight) (F : ℤ → ℂ)
    (a b : CircleT → ℂ) (hF : MemL2 F) (himg : IsNLFTImage F a b)
    (hout : IsOuterInD W (starFun a)) {ε : ℝ} (hε : 0 < ε)
    (hb : AWnorm W b < Real.sqrt 2 / 2 - ε) :
    ∃ C : ℝ, 0 < C ∧
      L1wNorm W F ≤ (C / ε) * AWnorm W (fun x => b x / a x)
```
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- The numerical threshold of Proposition 2 of arXiv:2603.02021v1, p.3, is
strictly below one: `1/√2 = √2/2 < 1`.  This is what lets the hypothesis
`‖b‖_{A_w} < 1/√2 − ε` with `ε > 0` fall inside the range of Lemma 6. -/
theorem sqrt_two_half_lt_one : Real.sqrt 2 / 2 < 1 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlt : Real.sqrt 2 < 2 := by nlinarith
  linarith

/-- The hypothesis of Proposition 2 (arXiv:2603.02021v1, p.3) implies the
strict smallness used downstream: if `r < 1/√2 − ε` with `ε > 0`, then `r < 1`.
In the paper `r = ‖b‖²_{A_w}`; this is the step that makes the geometric series
in Lemma 6 and the Neumann inversion of Lemma 4 converge uniformly. -/
theorem small_b_hyp_lt_one {ε r : ℝ} (hε : 0 < ε) (hr : r < Real.sqrt 2 / 2 - ε) :
    r < 1 := by
  have h : Real.sqrt 2 / 2 < 1 := sqrt_two_half_lt_one
  linarith

end

end Qatlib.Papers.SU2Fourier26.MainResults
