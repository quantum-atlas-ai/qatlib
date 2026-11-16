/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.PrincIdeal09.MainResults.RegulatorDual

@[expose] public section


set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
# PrincIdeal09 — continued-fraction reconstruction in the regulator regime

Fixed source: Arthur Schmidt, arXiv:0912.4807v1, §4. Lemma 3 is stated on
p.6 and proved on p.7, following Algorithm 2.

The ratio estimate requires the sample numerator ordering `0 ≤ z₁ ≤ z₂` and
the reconstruction range `1 ≤ z₂ ≤ R / 4`, in addition to the sample equations
and error bounds. The conclusion fails without these numerical conditions.
For example, `R = 10`, `q = 101`, `z₁ = z₂ = 10`, `ω₁ = 1/2`, and `ω₂ = -1/2`
give ratio error `2/201`, which is greater than `1/200`.
-/

open Qatlib.Papers.PrincIdeal09.MainResults

set_option autoImplicit false
noncomputable section
open Classical

namespace Qatlib.Papers.PrincIdeal09.MainResults

/-- **Lemma 3 (pp.6–7), with the reconstruction range explicit.** Let `q > (R⁺)²` and let
`y_i = (q/R⁺) z_i + ω_i` with `|ω_i| ≤ 1/2` be the two Regulator-Dual samples.
Then `|y₁/y₂ − z₁/z₂| ≤ 1/(2z₂²)`.

The inequalities `0 ≤ z₁ ≤ z₂` and `1 ≤ z₂ ≤ R / 4` specify the numerical
regime needed by the continued-fraction estimate [Schmidt2009]. -/
theorem lemma3_continued_fraction
    (q R y1 y2 z1 z2 ω1 ω2 : ℝ)
    (hR : 0 < R) (hq : R ^ 2 < q)
    (hy2 : y2 ≠ 0)
    (hz1_0 : 0 ≤ z1) (hz1_z2 : z1 ≤ z2) (hz2_1 : 1 ≤ z2) (hz2_le : z2 ≤ R / 4)
    (hω1 : |ω1| ≤ 1 / 2) (hω2 : |ω2| ≤ 1 / 2)
    (hy1 : y1 = (q / R) * z1 + ω1) (hy2eq : y2 = (q / R) * z2 + ω2) :
    |y1 / y2 - z1 / z2| ≤ 1 / (2 * z2 ^ 2) := by
  exact lemma3_continued_fraction_regime q R y1 y2 z1 z2 ω1 ω2 hR hq hy2
    hz1_0 hz1_z2 hz2_1 hz2_le hω1 hω2 hy1 hy2eq

/-- The repaired reconstruction regime is satisfiable: `R = 8`, `q = 65`,
`z₁ = z₂ = 1`, and zero sample errors give the sample pair `y₁ = y₂ = 65/8`. -/
theorem reconstruction_witness :
    |((65 : ℝ) / 8) / ((65 : ℝ) / 8) - 1 / 1| ≤ 1 / (2 * (1 : ℝ) ^ 2) := by
  apply lemma3_continued_fraction 65 8 (65 / 8) (65 / 8) 1 1 0 0
    <;> norm_num

/-- Samples satisfying every original premise can violate the ratio estimate when the
reconstruction range is absent: the error `2/201` exceeds the proposed bound `1/200`. -/
theorem ratio_range_counterexample :
    (0 : ℝ) < 10 ∧ (10 : ℝ) ^ 2 < 101 ∧
      (201 : ℝ) / 2 ≠ 0 ∧ (10 : ℝ) ≠ 0 ∧
      |(1 : ℝ) / 2| ≤ 1 / 2 ∧ |-(1 : ℝ) / 2| ≤ 1 / 2 ∧
      (203 : ℝ) / 2 = (101 / 10) * 10 + 1 / 2 ∧
      (201 : ℝ) / 2 = (101 / 10) * 10 - 1 / 2 ∧
      ¬ |((203 : ℝ) / 2) / ((201 : ℝ) / 2) - 10 / 10| ≤
        1 / (2 * (10 : ℝ) ^ 2) := by
  norm_num

end Qatlib.Papers.PrincIdeal09.MainResults
